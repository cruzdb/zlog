#include <atomic>
#include <condition_variable>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <thread>
#include <unordered_map>
#include <vector>
#include <boost/asio.hpp>
#include <boost/bind.hpp>
#include <boost/program_options.hpp>
#include "proto/zlog.pb.h"
#include "libzlog/log_impl.h"

namespace po = boost::program_options;

static std::string iops_logfile;

static int report_sec;

#if __APPLE__
static uint64_t get_time()
{
  struct timeval tv;
  gettimeofday(&tv, NULL);
  uint64_t res = tv.tv_sec * 1000000000ULL;
  return res + tv.tv_usec * 1000ULL;
}
#else
static uint64_t get_time(void)
{
  struct timespec ts;
  int ret = clock_gettime(CLOCK_MONOTONIC, &ts);
  assert(ret == 0);
  (void)ret;
  uint64_t nsec = ((uint64_t)ts.tv_sec) * ((uint64_t)1000000000);
  nsec += ts.tv_nsec;
  return nsec;
}
#endif

template <class T>
inline void hash_combine(std::size_t& seed, const T& v)
{
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

/*
 * TODO: currently the sequencer uses "pool" as a way to identify log state. But
 * now with pluggable storage backends, the "pool" concept is not generic. Until
 * we redesign the sequencer/client protocol, we'll just do equality on the meta
 * object which contains info about hwo to connect to a backend. This will be
 * slow, with potentially lots of correctness issues, but will get us to the
 * next step.
 */
typedef std::map<std::string, std::string> meta_t;

namespace std
{
  template<> struct hash<std::pair<meta_t, std::string>>
  {
    typedef std::pair<meta_t, std::string> argument_type;
    typedef std::size_t result_type;
    result_type operator()(argument_type const& s) const
    {
      result_type seed(std::hash<std::string>{}(s.second));
      for (auto e : s.first) {
        hash_combine(seed, e.first);
        hash_combine(seed, e.second);
      }
      return seed;
    }
  };
}

static meta_t get_meta(zlog_proto::MSeqRequest& req)
{
  meta_t meta;
  for (int i = 0; i < req.meta_size(); i++) {
    auto kv = req.meta(i);
    meta[kv.key()] = kv.val();
  }
  return meta;
}

/*
 * The sequence tracks the current sequence number. A read() returns the next
 * tail value, that is, the value returned from the next call to next(). So,
 * a read on an empty log will return 0 and the first sequence number returned
 * will be 0 (whenever next is called).
 */
class Sequence {
 public:
  Sequence(uint64_t seq, meta_t meta,
      std::string name, uint64_t epoch) :
    seq_(seq), meta_(meta), name_(name),
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

  inline int match(const meta_t& meta,
      const std::string& name,
      const uint64_t epoch) const {
    if (meta != meta_ || name != name_)
      return -EINVAL;
    if (epoch < epoch_)
      return -ERANGE;
    return 0;
  }

 private:
  std::mutex lock_;
  std::atomic<uint64_t> seq_;
  meta_t meta_;
  std::string name_;
  uint64_t epoch_;
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
  int ReadSequence(const meta_t& meta, const std::string& name,
      uint64_t epoch, bool increment, std::vector<uint64_t>& positions,
      int count, Sequence **cached_seq)
  {
    std::unique_lock<std::mutex> g(lock_);

    auto it = logs_.find(std::make_pair(meta, name));

    if (it == logs_.end()) {
      QueueLogInit(meta, name);
      return -EAGAIN;
    }

    if (epoch < it->second.epoch)
      return -ERANGE;

    if (increment)
      it->second.seq->next(positions, count);
    else {
      assert(count == 1);
      uint64_t seq = it->second.seq->read();
      positions.push_back(seq);
    }

    *cached_seq = it->second.seq;

    return 0;
  }

 private:
  struct Log {
    Log() {}
    Log(uint64_t pos, uint64_t epoch,
        meta_t meta, std::string name) :
      seq(new Sequence(pos, meta, name, epoch)), epoch(epoch)
    {}

    Sequence *seq;
    uint64_t epoch;
  };

  std::map<std::string, std::shared_ptr<zlog::Backend>> loaded_backends_;

  /*
   * Prepare the log for this sequencer. After this function runs a new
   * epoch has been allocated, each storage device is sealed with the new
   * epoch, and the maximum position written to prior to the new epoch is
   * found. The sequencer must not be allowed to hand out new positions until
   * these steps are completed successfully.
   */
  int InitLog(const meta_t& meta, const std::string& name,
      uint64_t *pepoch, uint64_t *pposition) {

    // which backend?
    if (meta.count("scheme") == 0) {
      std::cerr << "no scheme found" << std::endl;
      return -EINVAL;
    }
    auto scheme = meta.at("scheme");

    // TODO: on some distributions loading the same protobuf multiple times
    // leads to an error (see https://github.com/cruzdb/zlog/issues/187). the
    // true parameter in LogImpl::Open causes an extra reference to be taken on
    // the backend which prevents it from being unloaded. This means that we
    // never actually unload a loaded backend. This is silly, but figuring out
    // the proper linking etc... is becoming a time suck. This will 'work' for
    // now.
    bool extra_ref = loaded_backends_.find(scheme) == loaded_backends_.end();

    std::shared_ptr<zlog::Backend> backend;
    zlog::LogImpl *log;
    int ret = zlog::LogImpl::Open(scheme, name, meta, &log, &backend);
    if (extra_ref && backend)
        loaded_backends_[scheme] = backend;
    if (ret) {
      std::cerr << "failed to open log " << ret << std::endl;
      return ret;
    }

    // TODO
    //  - call propose_sequencer(...)
    //  - wait for new view to be read from log
    //  - check cookie
    //  - start serving

    // uint64_t epoch;
    // uint64_t position;
    // bool empty;
    // TODO: this is where we seal and get a new max pos.
    // delete log if errors
    assert(0);

    //*pepoch = epoch;
    //if (empty)
    //  *pposition = 0;
    //else
    //  *pposition = position + 1;

    delete log;

    return 0;
  }

  /*
   * Queue a log to be initialized.
   */
  void QueueLogInit(const meta_t& meta, const std::string& name) {
    pending_logs_.insert(std::make_pair(meta, name));
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

        for (auto it = logs_.begin(); it != logs_.end(); it++) {
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

        for (auto it = logs_.begin(); it != logs_.end(); it++) {
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
      meta_t meta;
      std::string name;

      {
        std::unique_lock<std::mutex> g(lock_);
        while (pending_logs_.empty())
          cond_.wait(g);
        auto it = pending_logs_.begin();
        assert(it != pending_logs_.end());
        meta = it->first;
        name = it->second;
      }

      uint64_t position;
      // assignment to only for uniitialized use error. InitLog always sets
      // epoch when it returns zero, so epoch use below in the next block is
      // safe.
      uint64_t epoch = 0;
      int ret = InitLog(meta, name, &epoch, &position);
      if (ret) {
        std::unique_lock<std::mutex> g(lock_);
        pending_logs_.erase(std::make_pair(meta, name));
        std::cerr << "failed to init log" << std::endl;
        continue;
      }

      {
        std::unique_lock<std::mutex> g(lock_);
        std::pair<meta_t, std::string> key = std::make_pair(meta, name);
        assert(pending_logs_.count(key) == 1);
        pending_logs_.erase(key);
        assert(logs_.count(key) == 0);
        Log log(position, epoch, meta, name);
        logs_[key] = log;
      }
    }
  }

  std::thread thread_;
  std::thread bench_thread_;
  std::mutex lock_;
  std::condition_variable cond_;
  std::unordered_map<std::pair<meta_t, std::string>, LogManager::Log > logs_;
  std::set<std::pair<meta_t, std::string> > pending_logs_;
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

    uint32_t tmp;
    memcpy(&tmp, (void*)buffer_, sizeof(tmp));
    uint32_t msg_size = ntohl(tmp);

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

    if (cached_seq) {
      auto meta = get_meta(req_);
      ret = cached_seq->match(meta, req_.name(), req_.epoch());
      if (!ret) {
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
      } else {
        if (req_.count() > 1)
          assert(req_.next());
        auto meta = get_meta(req_);
        ret = log_mgr->ReadSequence(meta, req_.name(),
            req_.epoch(), req_.next(), positions, req_.count(),
            &cached_seq);
      }
    } else {
      if (req_.count() > 1)
        assert(req_.next());
      auto meta = get_meta(req_);
      ret = log_mgr->ReadSequence(meta, req_.name(),
          req_.epoch(), req_.next(), positions, req_.count(),
          &cached_seq);
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

    assert(reply_.IsInitialized());

    uint32_t msg_size = reply_.ByteSize();
    assert(msg_size < sizeof(buffer_));
    if (!reply_.SerializeToArray(buffer_, msg_size)) {
      std::cerr << "failed to serialize message" << std::endl;
      exit(1);
    }

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
