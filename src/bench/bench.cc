#include <atomic>
#include <cassert>
#include <condition_variable>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <boost/program_options.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <signal.h>
#include <time.h>
#include <rados/librados.hpp>
#include "../include/zlog/log.h"

namespace po = boost::program_options;

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  int ret = clock_gettime(clock, &ts);
  assert(ret == 0);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getns()
{
  return __getns(CLOCK_MONOTONIC);
}

static volatile int stop;
static void sigint_handler(int sig) {
  stop = 1;
}

static std::atomic<uint64_t> ios_completed;
static std::atomic<uint64_t> outstanding_ios;
static std::condition_variable io_cond;
static std::mutex io_lock;

struct aio_state {
  zlog::AioCompletion *c;
};

static void handle_aio_cb(aio_state *io)
{
  // notify workload to gen more ios
  io_lock.lock();
  outstanding_ios--;
  io_lock.unlock();
  io_cond.notify_one();

  // clean-up
  assert(io->c->ReturnValue() == 0);
  delete io->c;
  io->c = NULL;

  ios_completed++;

  delete io;
}

static void workload(zlog::Log *log, const int qdepth, int entry_size)
{
  // create random data to use for payloads
  size_t rand_buf_size = 1ULL<<23;
  std::string rand_buf;
  rand_buf.reserve(rand_buf_size);
  std::ifstream ifs("/dev/urandom", std::ios::binary | std::ios::in);
  std::copy_n(std::istreambuf_iterator<char>(ifs),
      rand_buf_size, std::back_inserter(rand_buf));
  const char *rand_buf_raw = rand_buf.c_str();

  // grab random slices from the random bytes
  std::default_random_engine generator;
  std::uniform_int_distribution<int> rand_dist;
  rand_dist = std::uniform_int_distribution<int>(0,
      rand_buf_size - entry_size - 1);

  outstanding_ios = 0;
  std::unique_lock<std::mutex> lock(io_lock);
  for (;;) {
    while (outstanding_ios < (unsigned)qdepth) {

      // create aio context
      aio_state *io = new aio_state;
      io->c = zlog::Log::aio_create_completion(
          std::bind(handle_aio_cb, io));
      assert(io->c);

      // fill with random data
      ceph::bufferlist bl;
      size_t buf_offset = rand_dist(generator);
      bl.append(rand_buf_raw + buf_offset, entry_size);

      // queue aio append operation
      int ret = log->AioAppend(io->c, bl);
      assert(ret == 0);

      outstanding_ios++;
    }

    io_cond.wait(lock, [&]{ return outstanding_ios < (unsigned)qdepth || stop; });

    if (stop)
      return;
  }

  for (;;) {
    std::cout << "draining ios: " << outstanding_ios << " remaining" << std::endl;
    if (outstanding_ios == 0)
      break;
    sleep(1);
  }
}

static void report(int stats_window, const std::string tp_log_fn)
{
  ios_completed = 0;
  uint64_t window_start = getns();

  // open the output stream
  int fd = -1;
  if (!tp_log_fn.empty()) {
    fd = open(tp_log_fn.c_str(), O_WRONLY|O_CREAT|O_TRUNC, 0440);
    assert(fd != -1);
  }

  while (!stop) {
    sleep(stats_window);

    uint64_t ios_completed_in_window = ios_completed.exchange(0);
    uint64_t window_end = getns();
    uint64_t window_dur = window_end - window_start;
    window_start = window_end;

    double iops = (double)(ios_completed_in_window *
        1000000000ULL) / (double)window_dur;

    time_t now = time(NULL);

    if (stop)
      break;

    if (fd != -1) {
      dprintf(fd, "time %llu iops %llu\n",
          (unsigned long long)now,
          (unsigned long long)iops);
    }

    std::cout << "time " << now << " iops " << (int)iops << std::endl;
  }

  if (fd != -1) {
    fsync(fd);
    close(fd);
  }
}

int main(int argc, char **argv)
{
  std::string pool;
  std::string logname;
  std::string server;
  std::string port;
  int runtime;
  int stats_window;
  int qdepth;
  std::string tp_log_fn;
  int entry_size;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&logname)->default_value(""), "Log name")
    ("server", po::value<std::string>(&server)->default_value("localhost"), "Server host")
    ("port", po::value<std::string>(&port)->default_value("5678"), "Server port")
    ("runtime", po::value<int>(&runtime)->default_value(0), "runtime")
    ("window", po::value<int>(&stats_window)->default_value(2), "stats collection period")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "aio queue depth")
    ("iops-log", po::value<std::string>(&tp_log_fn)->default_value(""), "throughput log file")
    ("entry-size", po::value<int>(&entry_size)->default_value(1024), "Entry size")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  if (logname.empty()) {
    std::stringstream ss;
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    ss << uuid;
    ss << ".log";
    logname = ss.str();
  }

  std::cout << "      pool: " << pool << std::endl;
  std::cout << "   logname: " << logname << std::endl;
  std::cout << " seqr-host: " << server << std::endl;
  std::cout << " seqr-port: " << port << std::endl;
  std::cout << "   runtime: " << runtime << std::endl;
  std::cout << "  stat win: " << stats_window << std::endl;
  std::cout << "    qdepth: " << qdepth << std::endl;
  std::cout << "  iops log: " << tp_log_fn << std::endl;
  std::cout << "entry size: " << entry_size << std::endl;

  assert(!pool.empty());
  assert(runtime >= 0);
  assert(stats_window > 0);
  assert(qdepth > 0);
  assert(entry_size >= 0);

  // connect to rados
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool i/o context
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  // connect to the sequencer
  zlog::SeqrClient client(server.c_str(), port.c_str());
  client.Connect();

  // open log
  zlog::Log *log;
  ret = zlog::Log::OpenOrCreate(ioctx, logname, &client, &log);
  assert(ret == 0);

  // this is a little hack that refreshes the epoch we are storing so that
  // when we send out of a bunch of async requests they don't all initially
  // fail due to an old epoch. TODO: this should probably be handled when we
  // open the log?? TODO: try without this...
  ceph::bufferlist bl;
  log->Append(bl);

  signal(SIGINT, sigint_handler);

  stop = 0;

  std::thread report_runner(report, stats_window, tp_log_fn);
  std::thread workload_runner(workload, log, qdepth, entry_size);

  if (runtime) {
    sleep(runtime);
    stop = 1;
  }

  report_runner.join();
  workload_runner.join();

  ioctx.close();
  cluster.shutdown();

  return 0;
}
