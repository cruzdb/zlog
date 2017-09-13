#include <atomic>
#include <condition_variable>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <thread>
#include <vector>
#include <boost/asio.hpp>
#include <boost/bind.hpp>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "proto/zlog.pb.h"
#include "libzlog/log_impl.h"
#include "include/zlog/backend/ceph.h"

namespace po = boost::program_options;

static bool stream_support;

static std::string iops_logfile;

static int report_sec;

static uint64_t get_time(void)
{
  struct timespec ts;
  int ret = clock_gettime(CLOCK_MONOTONIC, &ts);
  assert(ret == 0);
  uint64_t nsec = ((uint64_t)ts.tv_sec) * ((uint64_t)1000000000);
  nsec += ts.tv_nsec;
  return nsec;
}

/*
 * The sequence tracks the current sequence number. A read() returns the next
 * tail value, that is, the value returned from the next call to next(). So,
 * a read on an empty log will return 0 and the first sequence number returned
 * will be 0 (whenever next is called).
 */
class Sequence {
 public:
  Sequence(uint64_t seq, std::string pool,
      std::string name, uint64_t epoch) :
    seq_(seq), pool_(pool), name_(name),
    epoch_(epoch)
  {}

  uint64_t read() {
    return seq_;
  }

  uint64_t next() {
    uint64_t prev = seq_.fetch_add(1);
    return prev;
  }

  void next(std::vector<uint64_t>& positions, int count) {
    assert(count > 0);
    uint64_t prev = seq_.fetch_add(count);
    for (uint64_t i = 0; i < (uint64_t)count; i++) {
      positions.push_back(prev + i);
    }
  }

  /*
   * the lock used limits concurrent queries and updates related to the
   * streaming interface. the actual next position is still atomic with
   * respect to other log users which can operate concurrently. one potential
   * optimization would be a lock per stream.
   */
  int stream_next(const std::vector<uint64_t>& stream_ids,
      std::vector<std::vector<uint64_t>>& stream_backpointers,
      uint64_t *pposition)
  {
    std::lock_guard<std::mutex> l(lock_);

    std::vector<std::vector<uint64_t>> result;

    // make a copy of the current backpointers
    for (std::vector<uint64_t>::const_iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {

      uint64_t stream_id = *it;
      stream_index_t::const_iterator stream_it = streams_.find(stream_id);
      if (stream_it == streams_.end()) {
        /*
         * If a stream doesn't exist initialize an empty set of backpointers.
         * How do we know a stream doesn't exist? During log initialization we
         * setup all existing logs...
         */
        streams_[stream_id] = stream_backpointers_t();

        std::vector<uint64_t> ptrs;
        result.push_back(ptrs);
        continue;
      }

      std::vector<uint64_t> ptrs(stream_it->second.begin(),
          stream_it->second.end());
      result.push_back(ptrs);
    }

    uint64_t next_pos = next();

    // add new position to each stream
    for (std::vector<uint64_t>::const_iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_backpointers_t& backpointers = streams_.at(stream_id);
      backpointers.push_back(next_pos);
      if (backpointers.size() > 10)
        backpointers.pop_front();
    }

    *pposition = next_pos;
    stream_backpointers.swap(result);

    return 0;
  }

  int stream_read(const std::vector<uint64_t>& stream_ids,
      std::vector<std::vector<uint64_t>>& stream_backpointers,
      uint64_t *pposition)
  {
    std::lock_guard<std::mutex> l(lock_);

    std::vector<std::vector<uint64_t>> result;

    // make a copy of the current backpointers
    for (std::vector<uint64_t>::const_iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {

      uint64_t stream_id = *it;
      stream_index_t::const_iterator stream_it = streams_.find(stream_id);
      if (stream_it == streams_.end()) {
        /*
         * If a stream doesn't exist initialize an empty set of backpointers.
         * How do we know a stream doesn't exist? During log initialization we
         * setup all existing logs...
         */
        streams_[stream_id] = stream_backpointers_t();

        std::vector<uint64_t> ptrs;
        result.push_back(ptrs);
        continue;
      }

      std::vector<uint64_t> ptrs(stream_it->second.begin(),
          stream_it->second.end());
      result.push_back(ptrs);
    }

    *pposition = read();
    stream_backpointers.swap(result);

    return 0;
  }

  inline int match(const std::string& pool,
      const std::string& name,
      const uint64_t epoch) const {
    if (pool != pool_ || name != name_)
      return -EINVAL;
    if (epoch < epoch_)
      return -ERANGE;
    return 0;
  }

  void set_streams(std::map<uint64_t, std::deque<uint64_t>>& ptrs) {
    streams_.swap(ptrs);
  }

 private:
  typedef std::deque<uint64_t> stream_backpointers_t;
  typedef std::map<uint64_t, stream_backpointers_t> stream_index_t;

  std::mutex lock_;
  std::atomic<uint64_t> seq_;
  std::string pool_;
  std::string name_;
  uint64_t epoch_;

  stream_index_t streams_;
};

class LogManager {
 public:
  LogManager() {
    thread_ = std::thread(&LogManager::Run, this);
    if (report_sec > 0)
      bench_thread_ = std::thread(&LogManager::BenchMonitor, this);
  }

  /*
   * Read and optionally increment the log sequence number.
   */
  int ReadSequence(const std::string& pool, const std::string& name,
      uint64_t epoch, bool increment, std::vector<uint64_t>& positions,
      int count, const std::vector<uint64_t>& stream_ids,
      std::vector<std::vector<uint64_t>>& stream_backpointers,
      Sequence **cached_seq)
  {
    std::unique_lock<std::mutex> g(lock_);

    std::map<std::pair<std::string, std::string>, Log>::iterator it =
      logs_.find(std::make_pair(pool, name));

    if (it == logs_.end()) {
      QueueLogInit(pool, name);
      return -EAGAIN;
    }

    if (epoch < it->second.epoch)
      return -ERANGE;

    if (stream_ids.size() == 0) {
      if (increment)
        it->second.seq->next(positions, count);
      else {
        assert(count == 1);
        uint64_t seq = it->second.seq->read();
        positions.push_back(seq);
      }
    } else {
      int ret = 0;
      uint64_t seq;
      assert(count == 1);
      if (increment)
        ret = it->second.seq->stream_next(stream_ids, stream_backpointers, &seq);
      else
        ret = it->second.seq->stream_read(stream_ids, stream_backpointers, &seq);
      if (ret)
        return ret;
      positions.push_back(seq);
    }

    *cached_seq = it->second.seq;

    return 0;
  }

 private:
  struct Log {
    Log() {}
    Log(uint64_t pos, uint64_t epoch,
        std::string pool, std::string name,
        std::map<uint64_t, std::deque<uint64_t>>& ptrs) :
      seq(new Sequence(pos, pool, name, epoch)), epoch(epoch)
    {
      seq->set_streams(ptrs);
    }

    Sequence *seq;
    uint64_t epoch;
  };

  /*
   * Prepare the log for this sequencer. After this function runs a new
   * epoch has been allocated, each storage device is sealed with the new
   * epoch, and the maximum position written to prior to the new epoch is
   * found. The sequencer must not be allowed to hand out new positions until
   * these steps are completed successfully.
   */
  int InitLog(const std::string& pool, const std::string& name,
      uint64_t *pepoch, uint64_t *pposition,
      std::map<uint64_t, std::deque<uint64_t>>& ptrs) {

    librados::Rados rados;
    int ret = rados.init(NULL);
    if (ret) {
      std::cerr << "could not initialize rados client" << std::endl;
      return ret;
    }

    rados.conf_read_file(NULL);
    rados.conf_parse_env(NULL);

    ret = rados.connect();
    if (ret) {
      std::cerr << "rados client could not connect" << std::endl;
      return ret;
    }

    librados::IoCtx ioctx;
    ret = rados.ioctx_create(pool.c_str(), ioctx);
    if (ret) {
      std::cerr << "failed to connect to pool " << pool
        << " ret " << ret << std::endl;
      return ret;
    }

    CephBackend *be = new CephBackend(&ioctx);

    zlog::Log *baselog;
    ret = zlog::Log::Open(be, name, NULL, &baselog);
    if (ret) {
      std::cerr << "failed to open log " << name << std::endl;
      return ret;
    }
    zlog::LogImpl *log = reinterpret_cast<zlog::LogImpl*>(baselog);

    uint64_t epoch;
    uint64_t position;
    bool empty;
    ret = log->CreateCut(&epoch, &position, &empty);
    if (ret) {
      std::cerr << "failed to create cut ret " << ret << std::endl;
      return ret;
    }

    /*
     * This is very inefficient. Basically during log initialization we just
     * scan the entire thing to initialize the streams. Right now we need
     * something working and can bite the initialization cost and make things
     * more dynamic and efficient during a later rewrite of the streaming
     * interface.
     */
    if (stream_support && !empty) {
      uint64_t tail = position;
      std::map<uint64_t, std::deque<uint64_t>> ptrs_out;
      for (;;) {
        for (;;) {
          std::set<uint64_t> stream_ids;
          ret = log->StreamMembership(epoch, stream_ids, tail);
          if (ret == 0) {
            for (auto it = stream_ids.begin(); it != stream_ids.end(); it++) {
              auto it2 = ptrs_out.find(*it);
              if (it2 == ptrs_out.end() || it2->second.size() < 10)
                ptrs_out[*it].push_back(tail);
            }
            break;
          } else if (ret == -EINVAL) {
            // skip non-stream entries
            break;
          } else if (ret == -ENODATA) {
            // skip invalidated entries
            break;
          } else if (ret == -ENOENT) {
            // fill entries unwritten entries
            ret = log->Fill(epoch, tail);
            if (ret == 0) {
              // skip invalidated entries
              break;
            } else if (ret == -EROFS) {
              // retry
              continue;
            } else {
              std::cerr << "error initialing log stream: fill: " << ret << std::endl;
              return ret;
            }
          } else {
            std::cerr << "error initialing log stream: stream membership: " << ret << std::endl;
            return ret;
          }
        }
        if (tail)
          tail--;
        else
          break;
      }
      ptrs.swap(ptrs_out);
    }

    *pepoch = epoch;
    if (empty)
      *pposition = 0;
    else
      *pposition = position + 1;

    ioctx.close();
    rados.shutdown();

    return 0;
  }

  /*
   * Queue a log to be initialized.
   */
  void QueueLogInit(const std::string& pool, const std::string& name) {
    pending_logs_.insert(std::make_pair(pool, name));
    cond_.notify_one();
  }

  /*
   * Monitors the performance of the sequencer.
   *
   * It looks at all the sequence states and then computes how many sequences
   * were handed out over a period of time.
   *
   * FIXME: Note that this currently doesn't take into account new logs that
   * are registered during the sleep period.
   */
  void BenchMonitor() {
    // open the output stream
    int fd = -1;
    if (!iops_logfile.empty()) {
      fd = open(iops_logfile.c_str(), O_WRONLY|O_CREAT|O_TRUNC, 0440);
      assert(fd != -1);
    }

    for (;;) {
      uint64_t start_ns;
      uint64_t start_seq;
      uint64_t num_logs_start;

      // starting state of all the current sequences
      {
        std::unique_lock<std::mutex> g(lock_);

        start_ns = get_time();
        start_seq = 0;

        std::map<std::pair<std::string, std::string>, LogManager::Log >::iterator it;
        for (it = logs_.begin(); it != logs_.end(); it++) {
          start_seq += it->second.seq->read();
        }

        num_logs_start = logs_.size();
      }

      assert(report_sec > 0);
      sleep(report_sec);

      uint64_t end_ns;
      uint64_t end_seq;
      uint64_t num_logs;

      // ending state of all the current sequences
      {
        std::unique_lock<std::mutex> g(lock_);

        end_seq = 0;
        num_logs = logs_.size();

        std::map<std::pair<std::string, std::string>, LogManager::Log >::iterator it;
        for (it = logs_.begin(); it != logs_.end(); it++) {
          end_seq += it->second.seq->read();
        }

        end_ns = get_time();
      }

      uint64_t elapsed_ns = end_ns - start_ns;
      uint64_t total_seqs = end_seq - start_seq;
      uint64_t rate = (total_seqs * 1000000000ULL) / elapsed_ns;

      double iops = (double)(total_seqs * 1000000000ULL) / (double)elapsed_ns;
      time_t now = time(NULL);

      if (num_logs_start == num_logs) {
        std::cout << "seqr rate = " << rate << " (" << iops << ") seqs/sec" << std::endl;
        if (fd != -1) {
          dprintf(fd, "%llu %llu\n",
              (unsigned long long)now,
              (unsigned long long)iops);
          fsync(fd);
        }
      } else
        std::cout << "seqr rate = " << rate << " seqs/sec (warn: log count change)" << std::endl;
    }

    if (fd != -1) {
      fsync(fd);
      close(fd);
    }
  }

  void Run() {
    for (;;) {
      std::string pool, name;

      {
        std::unique_lock<std::mutex> g(lock_);
        while (pending_logs_.empty())
          cond_.wait(g);
        std::set<std::pair<std::string, std::string> >::iterator it =
          pending_logs_.begin();
        assert(it != pending_logs_.end());
        pool = it->first;
        name = it->second;
      }

      uint64_t position, epoch;
      std::map<uint64_t, std::deque<uint64_t>> ptrs;
      int ret = InitLog(pool, name, &epoch, &position, ptrs);
      if (ret) {
        std::unique_lock<std::mutex> g(lock_);
        pending_logs_.erase(std::make_pair(pool, name));
        std::cerr << "failed to init log" << std::endl;
        continue;
      }

      {
        std::unique_lock<std::mutex> g(lock_);
        std::pair<std::string, std::string> key = std::make_pair(pool, name);
        assert(pending_logs_.count(key) == 1);
        pending_logs_.erase(key);
        assert(logs_.count(key) == 0);
        Log log(position, epoch, pool, name, ptrs);
        logs_[key] = log;
      }
    }
  }

  std::thread thread_;
  std::thread bench_thread_;
  std::mutex lock_;
  std::condition_variable cond_;
  std::map<std::pair<std::string, std::string>, LogManager::Log > logs_;
  std::set<std::pair<std::string, std::string> > pending_logs_;
};

static LogManager *log_mgr;

class Session {
 public:
  Session(boost::asio::io_service& io_service)
    : socket_(io_service)
  {
    cached_seq = NULL;
  }

  boost::asio::ip::tcp::socket& socket() {
    return socket_;
  }

  void start() {
    boost::asio::async_read(socket_,
        boost::asio::buffer(buffer_, sizeof(uint32_t)),
        boost::bind(&Session::handle_hdr, this,
          boost::asio::placeholders::error,
          boost::asio::placeholders::bytes_transferred));
  }

 private:
  void handle_hdr(const boost::system::error_code& err, size_t size) {
    if (err) {
      delete this;
      return;
    }

    uint32_t msg_size = ntohl(*((uint32_t*)buffer_));

    if (msg_size > sizeof(buffer_)) {
      std::cerr << "message is too large" << std::endl;
      delete this;
      return;
    }

    boost::asio::async_read(socket_,
        boost::asio::buffer(buffer_, msg_size),
        boost::bind(&Session::handle_msg, this,
          boost::asio::placeholders::error,
          boost::asio::placeholders::bytes_transferred));
  }

  void handle_msg(const boost::system::error_code& err, size_t size) {
    if (err) {
      delete this;
      return;
    }

    req_.Clear();

    if (!req_.ParseFromArray(buffer_, size)) {
      std::cerr << "failed to parse message" << std::endl;
      delete this;
      return;
    }

    if (!req_.IsInitialized()) {
      std::cerr << "received incomplete message" << std::endl;
      delete this;
      return;
    }

    reply_.Clear();

    /*
     * Try to do a fast sequencer read. The basic idea is that for a
     * particular session a client will likely be referencing the same log
     * repeatedly.
     *
     * 1. if we haven't cached a sequencer then do a slow lookup which will
     * search for it in an index and return a pointer to the sequencer object.
     *
     * 2. If we have a cached sequencer object then check to see if it is for
     * the correct pool/name/epoch. If so, read directly.
     *
     * 3. Otherwise, do a slow lookup and update the cached sequencer.
     *
     * Important:
     *  - This is currently safe because once a sequencer object is created
     *  it is never modified. But for instance we might want to change a
     *  configuraiton and update the epoch. We may also need to add a
     *  generation number and reference counting to deal with logs that come
     *  and go. Currently they are created and never deleted.
     */
    int ret;
    std::vector<uint64_t> positions;
    assert(req_.count() > 0 && req_.count() < 100);

    // per-stream backpointers
    std::vector<std::vector<uint64_t>> stream_backpointers;
    const std::vector<uint64_t> stream_ids(req_.stream_ids().begin(),
        req_.stream_ids().end());

    if (cached_seq) {
      ret = cached_seq->match(req_.pool(), req_.name(), req_.epoch());
      if (!ret) {
        /*
         * If this request doesn't contain any stream ids then we are only
         * interacting with the log tail (i.e. query or increment).
         */
        if (req_.stream_ids_size() == 0) {
          /*
           * If only one position is being requested then it might be a query
           * or an increment request.
           */
          if (req_.count() == 1) {
            uint64_t seq;
            if (req_.next())
              seq = cached_seq->next();
            else
              seq = cached_seq->read();
            positions.push_back(seq);
          } else {
            /*
             * When the count is larger than 1 then it must be a request for
             * multiple new positions.
             */
            assert(req_.next());
            cached_seq->next(positions, req_.count());
          }
        } else { // req_.stream_ids_size() > 0
          /*
           * This is a request involving streams, and might be a query or a
           * request for incrementing the log tail.
           */

          /*
           * this is very rude... well, the current support for streams
           * contains some cases that cause major delays while processing log
           * entries and stream support is pre-alpha stage, so we've added a
           * mode that assumes no clients with use the stream api.
           *
           * consider yourself warned.
           */
          assert(stream_support);

          // batch stream requests not yet supported
          assert(req_.count() == 1);

          /*
           * If a stream hasn't been initialized then we may return -EAGAIN
           * and instruct the client to try again later.
           */
          uint64_t seq;
          if (req_.next())
            ret = cached_seq->stream_next(stream_ids, stream_backpointers, &seq);
          else
            ret = cached_seq->stream_read(stream_ids, stream_backpointers, &seq);
          positions.push_back(seq);
        }
      } else {
        if (req_.count() > 1)
          assert(req_.next());
        ret = log_mgr->ReadSequence(req_.pool(), req_.name(),
            req_.epoch(), req_.next(), positions, req_.count(),
            stream_ids, stream_backpointers, &cached_seq);
      }
    } else {
      if (req_.count() > 1)
        assert(req_.next());
      ret = log_mgr->ReadSequence(req_.pool(), req_.name(),
          req_.epoch(), req_.next(), positions, req_.count(),
          stream_ids, stream_backpointers, &cached_seq);
    }

    if (ret == -EAGAIN)
      reply_.set_status(zlog_proto::MSeqReply::INIT_LOG);
    else if (ret == -ERANGE)
      reply_.set_status(zlog_proto::MSeqReply::STALE_EPOCH);
    else
      assert(!ret);

    for (std::vector<uint64_t>::const_iterator it = positions.begin();
         it != positions.end(); it++) {
      uint64_t pos = *it;
      reply_.add_position(pos);
    }

    size_t stream_index = 0;
    for (std::vector<std::vector<uint64_t>>::const_iterator it =
         stream_backpointers.begin(); it != stream_backpointers.end(); it++) {
      zlog_proto::StreamBackPointer *ptrs = reply_.add_stream_backpointers();
      ptrs->set_id(req_.stream_ids(stream_index++));
      for (std::vector<uint64_t>::const_iterator it2 = it->begin();
          it2 != it->end(); it2++) {
        uint64_t pos = *it2;
        ptrs->add_backpointer(pos);
      }
    }

    assert(reply_.IsInitialized());

    uint32_t msg_size = reply_.ByteSize();
    assert(msg_size < sizeof(buffer_));
    assert(reply_.SerializeToArray(buffer_, msg_size));

    // scatter/gather buffers
    std::vector<boost::asio::const_buffer> out;
    be_msg_size_ = htonl(msg_size);
    out.push_back(boost::asio::buffer(&be_msg_size_, sizeof(be_msg_size_)));
    out.push_back(boost::asio::buffer(buffer_, msg_size));

    boost::asio::async_write(socket_, out,
        boost::bind(&Session::handle_reply, this,
          boost::asio::placeholders::error,
          boost::asio::placeholders::bytes_transferred));
  }

  void handle_reply(const boost::system::error_code& err, size_t size) {
    if (err) {
      delete this;
      return;
    }

    start();
  }

  boost::asio::ip::tcp::socket socket_;

  char buffer_[1024];
  uint32_t be_msg_size_;

  zlog_proto::MSeqRequest req_;
  zlog_proto::MSeqReply reply_;

  Sequence *cached_seq;
};

class Server {
 public:
  Server(short port, std::size_t nthreads)
    : acceptor_(io_service_,
        boost::asio::ip::tcp::endpoint(
          boost::asio::ip::tcp::v4(), port)),
      nthreads_(nthreads)
  {
    acceptor_.set_option(boost::asio::ip::tcp::no_delay(true));
    start_accept();
  }

  void run() {
    std::vector<std::thread> threads;
    for (std::size_t i = 0; i < nthreads_; i++) {
      std::thread thread([&]{ io_service_.run(); });
      threads.push_back(std::move(thread));
    }

    for (std::size_t i = 0; i < threads.size(); ++i)
      threads[i].join();
  }

 private:
  void start_accept() {
    Session* new_session = new Session(io_service_);
    acceptor_.async_accept(new_session->socket(),
        boost::bind(&Server::handle_accept, this, new_session,
          boost::asio::placeholders::error));
  }

  void handle_accept(Session* new_session,
      const boost::system::error_code& error) {
    if (!error)
      new_session->start();
    else
      delete new_session;
    start_accept();
  }

  boost::asio::io_service io_service_;
  boost::asio::ip::tcp::acceptor acceptor_;
  std::size_t nthreads_;
};

int main(int argc, char* argv[])
{
  int port;
  std::string host;
  int nthreads;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("port", po::value<int>(&port)->required(), "Server port")
    ("nthreads", po::value<int>(&nthreads)->default_value(1), "Num threads")
    ("report-sec", po::value<int>(&report_sec)->default_value(0), "Time between rate reports")
    ("daemon,d", "Run in background")
    ("streams", po::bool_switch(&stream_support)->default_value(false), "support streams")
    ("iops-logfile", po::value<std::string>(&iops_logfile)->default_value(""), "iops log file")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  if (nthreads <= 0 || nthreads > 64)
    nthreads = 1;

  Server *s;

  if (vm.count("daemon")) {
    pid_t pid = fork();
    if (pid < 0) {
      exit(EXIT_FAILURE);
    }

    if (pid > 0) {
      exit(EXIT_SUCCESS);
    }

    s = new Server(port, nthreads);

    pid_t sid = setsid();
    if (sid < 0) {
      exit(EXIT_FAILURE);
    }

    umask(0);

    close(0);
    close(1);
    close(2);
  } else {
    s = new Server(port, nthreads);
  }

  log_mgr = new LogManager();

  s->run();

  return 0;
}
