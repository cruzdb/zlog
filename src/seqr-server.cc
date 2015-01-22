#include <cstdlib>
#include <iostream>
#include <vector>
#include <boost/shared_ptr.hpp>
#include <boost/bind.hpp>
#include <boost/asio.hpp>
#include <boost/program_options.hpp>
#include <boost/thread/thread.hpp>
#include <rados/librados.hpp>
#include "libzlog.h"
#include "zlog.pb.h"

namespace po = boost::program_options;

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

class Sequence {
 public:
  Sequence() : seq_(0) {}
  Sequence(uint64_t seq) : seq_(seq) {}

  uint64_t read() {
    return seq_;
  }

  void inc() {
    seq_++;
  }

 private:
  uint64_t seq_;
};

class LogManager {
 public:
  LogManager() {
    thread_ = boost::thread(&LogManager::Run, this);
    if (report_sec > 0)
      bench_thread_ = boost::thread(&LogManager::BenchMonitor, this);
  }

  /*
   * Read and optionally increment the log sequence number.
   */
  uint64_t ReadSequence(const std::string& pool, const std::string& name,
      uint64_t epoch, bool increment, uint64_t *seq) {

    boost::unique_lock<boost::mutex> g(lock_);

    std::map<std::pair<std::string, std::string>, Log>::iterator it =
      logs_.find(std::make_pair(pool, name));

    if (it == logs_.end()) {
      QueueLogInit(pool, name);
      return -EAGAIN;
    }

    if (epoch < it->second.epoch)
      return -ERANGE;

    if (increment)
      it->second.seq.inc();

    *seq = it->second.seq.read();

    return 0;
  }

 private:
  struct Log {
    Log() {}
    Log(uint64_t pos, uint64_t epoch) : seq(pos), epoch(epoch) {}
    Sequence seq;
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
      uint64_t *pepoch, uint64_t *pposition) {

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

    zlog::Log log;
    ret = zlog::Log::Open(ioctx, name, NULL, log);
    if (ret) {
      std::cerr << "failed to open log " << name << std::endl;
      return ret;
    }

    uint64_t epoch;
    ret = log.SetProjection(&epoch);
    if (ret) {
      std::cerr << "failed to set new projection " << ret << std::endl;
      return ret;
    }

    ret = log.Seal(epoch);
    if (ret) {
      std::cerr << "failed to seal the store " << ret << std::endl;
      return ret;
    }

    uint64_t position;
    ret = log.FindMaxPosition(epoch, &position);
    if (ret) {
      std::cerr << "failed to find max position " << ret << std::endl;
      return ret;
    }

    *pepoch = epoch;
    *pposition = position;

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
    for (;;) {
      uint64_t start_ns;
      uint64_t start_seq;

      // starting state of all the current sequences
      {
        boost::unique_lock<boost::mutex> g(lock_);

        start_ns = get_time();
        start_seq = 0;

        std::map<std::pair<std::string, std::string>, LogManager::Log >::iterator it;
        for (it = logs_.begin(); it != logs_.end(); it++) {
          start_seq += it->second.seq.read();
        }
      }

      assert(report_sec > 0);
      sleep(report_sec);

      uint64_t end_ns;
      uint64_t end_seq;
      int num_logs;

      // ending state of all the current sequences
      {
        boost::unique_lock<boost::mutex> g(lock_);

        end_ns = get_time();
        end_seq = 0;
        num_logs = logs_.size();

        std::map<std::pair<std::string, std::string>, LogManager::Log >::iterator it;
        for (it = logs_.begin(); it != logs_.end(); it++) {
          end_seq += it->second.seq.read();
        }
      }

      uint64_t elapsed_ns = end_ns - start_ns;
      uint64_t total_seqs = end_seq - start_seq;
      uint64_t rate = (total_seqs * 1000000000ULL) / elapsed_ns;
      std::cout << "seqr rate = " << rate << " seqs/sec" << std::endl;
    }
  }

  void Run() {
    for (;;) {
      std::string pool, name;

      {
        boost::unique_lock<boost::mutex> g(lock_);
        while (pending_logs_.empty())
          cond_.wait(g);
        std::set<std::pair<std::string, std::string> >::iterator it =
          pending_logs_.begin();
        assert(it != pending_logs_.end());
        pool = it->first;
        name = it->second;
      }

      uint64_t position, epoch;
      int ret = InitLog(pool, name, &epoch, &position);
      if (ret) {
        boost::unique_lock<boost::mutex> g(lock_);
        pending_logs_.erase(std::make_pair(pool, name));
        std::cerr << "failed to init log" << std::endl;
        continue;
      }

      {
        boost::unique_lock<boost::mutex> g(lock_);
        std::pair<std::string, std::string> key = std::make_pair(pool, name);
        assert(pending_logs_.count(key) == 1);
        pending_logs_.erase(key);
        assert(logs_.count(key) == 0);
        Log log(position, epoch);
        logs_[key] = log;
      }
    }
  }

  boost::thread thread_;
  boost::thread bench_thread_;
  boost::mutex lock_;
  boost::condition_variable cond_;
  std::map<std::pair<std::string, std::string>, LogManager::Log > logs_;
  std::set<std::pair<std::string, std::string> > pending_logs_;
};

static LogManager *log_mgr;

class Session {
 public:
  Session(boost::asio::io_service& io_service)
    : socket_(io_service)
  {}

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

    uint64_t seq;

    int ret = log_mgr->ReadSequence(req_.pool(), req_.name(),
        req_.epoch(), req_.next(), &seq);
    if (ret == -EAGAIN)
      reply_.set_status(zlog_proto::MSeqReply::INIT_LOG);
    else if (ret == -ERANGE)
      reply_.set_status(zlog_proto::MSeqReply::STALE_EPOCH);
    else
      assert(!ret);

    reply_.set_position(seq);

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
    std::vector<boost::shared_ptr<boost::thread> > threads;
    for (std::size_t i = 0; i < nthreads_; i++) {
      boost::shared_ptr<boost::thread> thread(new boost::thread(
            boost::bind(&boost::asio::io_service::run, &io_service_)));
      threads.push_back(thread);
    }

    for (std::size_t i = 0; i < threads.size(); ++i)
      threads[i]->join();
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
