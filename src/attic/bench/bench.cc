#include <atomic>
#include <random>
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
#include "../libzlog/log_impl.h"
#include "include/zlog/backend/ceph.h"

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
  if (io->c->ReturnValue()) {
    std::cout << "error: io retval = " << io->c->ReturnValue() << std::endl;
    assert(io->c->ReturnValue() == 0);
    stop = 1;
    exit(1);
  }
  delete io->c;
  io->c = NULL;

  ios_completed++;

  delete io;
}

static void append_workload_func(zlog::Log *log, const int qdepth, int entry_size)
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
      size_t buf_offset = rand_dist(generator);

      // queue aio append operation
      int ret = log->AioAppend(io->c, zlog::Slice(rand_buf_raw + buf_offset, entry_size));
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

static void append_workload_sync_func(zlog::Log *log, int entry_size)
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

  for (;;) {
    // fill with random data
    size_t buf_offset = rand_dist(generator);

    uint64_t pos;
    int ret = log->Append(zlog::Slice(rand_buf_raw + buf_offset, entry_size), &pos);
    assert(ret == 0);

    ios_completed++;

    if (stop)
      break;
  }
}

static void nextseq_workload_func(zlog::LogImpl *log_impl)
{
  while (!stop) {
    uint64_t tail;
    int ret = log_impl->CheckTail(&tail, nullptr, true);
    assert(ret == 0);

    ios_completed++;
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

static void conflict(const po::variables_map& vm,
    const std::string& opt1, const std::string& opt2)
{
  if (vm.count(opt1) && !vm[opt1].defaulted() &&
      vm.count(opt2) && !vm[opt2].defaulted()) {
    throw std::logic_error(std::string("Conflicting options '") +
        opt1 + "' and '" + opt2 + "'.");
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
  int bev;
  int stripe_width;
  bool sync;

  bool append_workload;
  bool nextseq_workload;

  po::options_description gen_opts("General options");
  gen_opts.add_options()
    ("help,h", "show help message")
    ("append,a", po::bool_switch(&append_workload)->default_value(true), "append workload")
    ("nextseq,n", po::bool_switch(&nextseq_workload)->default_value(false), "next seq workload")
    ("logname,l", po::value<std::string>(&logname)->default_value(""), "Log name")
    ("server,s", po::value<std::string>(&server)->default_value("localhost"), "Server host")
    ("port,p", po::value<std::string>(&port)->default_value("5678"), "Server port")
    ("runtime,r", po::value<int>(&runtime)->default_value(0), "runtime")
    ("window", po::value<int>(&stats_window)->default_value(2), "stats collection period")
    ("pool,p", po::value<std::string>(&pool)->required(), "Pool name")
    ("iops-log", po::value<std::string>(&tp_log_fn)->default_value(""), "throughput log file")
    ("store-ver", po::value<int>(&bev)->default_value(1), "backend version")
    ("stripe-width", po::value<int>(&stripe_width)->default_value(-1), "stripe width")
    ("sync", po::bool_switch(&sync)->default_value(false), "use sync io")
  ;

  po::options_description append_opts("Append workload options");
  append_opts.add_options()
    ("entry-size,e", po::value<int>(&entry_size)->default_value(1024), "Entry size")
    ("qdepth,q", po::value<int>(&qdepth)->default_value(1), "aio queue depth")
  ;

  po::options_description all_opts("Allowed options");
  all_opts.add(gen_opts).add(append_opts);

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, all_opts), vm);

  if (vm.count("help")) {
    std::cout << all_opts << std::endl;
    return 1;
  }

  // choose only one workload
  conflict(vm, "append", "nextseq");

  // sequencer workload doesn't perform appends
  conflict(vm, "nextseq", "entry-size");

  po::notify(vm);

  if (logname.empty()) {
    std::stringstream ss;
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    ss << uuid;
    ss << ".log";
    logname = ss.str();
  }

  if (nextseq_workload)
    append_workload = false;

  std::string workload_name;
  if (append_workload)
    workload_name = "append";
  else if (nextseq_workload)
    workload_name = "next seq";
  else
    assert(0);

  std::cout << "  workload: " << workload_name << std::endl;
  std::cout << "      pool: " << pool << std::endl;
  std::cout << "   logname: " << logname << std::endl;
  std::cout << " seqr-host: " << server << std::endl;
  std::cout << " seqr-port: " << port << std::endl;
  std::cout << "   runtime: " << runtime << std::endl;
  std::cout << "  stat win: " << stats_window << std::endl;
  std::cout << "    qdepth: " << qdepth << std::endl;
  std::cout << "  iops log: " << tp_log_fn << std::endl;
  std::cout << "entry size: " << entry_size << std::endl;
  std::cout << " store ver: " << bev << std::endl;
  std::cout << "strp width: " << stripe_width << std::endl;
  std::cout << "   sync io: " << sync << std::endl;

  assert(!pool.empty());
  assert(runtime >= 0);
  assert(stats_window > 0);
  assert(qdepth > 0);
  assert(entry_size >= 0);
  assert(bev == 1 || bev == 2);
  assert(stripe_width == -1 || stripe_width > 0);

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
  std::cerr << "using outdated api: using exclusive writer mode, default stripe width" << std::endl;

  auto be = std::unique_ptr<zlog::Backend>(new zlog::storage::ceph::CephBackend(&ioctx));

  // open log
  zlog::Log *log;
  if (stripe_width == -1) {
    // default stripe width
    ret = zlog::Log::CreateWithBackend(std::move(be), logname, &log);
  } else {
    ret = zlog::Log::OpenWithBackend(std::move(be), logname, &log);
    if (ret == -ENOENT)
      ret = zlog::Log::CreateWithBackend(std::move(be), logname, &log);
#if 0
    if (ret == 0)
      assert(log->StripeWidth() == stripe_width);
#endif
  }
  assert(ret == 0);

  // used to access the low-level sequencer checktail interface
  zlog::LogImpl *log_impl = reinterpret_cast<zlog::LogImpl*>(log);

  // using a different backend version is a development feature and we don't
  // want to expose it through the public api yet. here we set the backend
  // version on the LogImpl object directly. All clients of the log must
  // choose the same version for every interaction with the log, and the
  // version must be set before any log I/O is performed by a client.
  switch (bev) {
    case 1:
      // this is the default case
      break;
    case 2:
      assert(0);
      exit(1);
    default:
      assert(0);
      exit(1);
  }

  // this is a little hack that refreshes the epoch we are storing so that
  // when we send out of a bunch of async requests they don't all initially
  // fail due to an old epoch. TODO: this should probably be handled when we
  // open the log?? TODO: try without this...
  log->Append(zlog::Slice());

  signal(SIGINT, sigint_handler);

  stop = 0;

  std::thread report_runner(report, stats_window, tp_log_fn);

  std::vector<std::thread> workload_runners;
  if (append_workload) {
    if (sync) {
      for (int i = 0; i < qdepth; i++) {
        workload_runners.push_back(std::thread(
              append_workload_sync_func, log, entry_size));
      }
    } else {
      workload_runners.push_back(std::thread(
            append_workload_func, log, qdepth, entry_size));
    }
  } else if (nextseq_workload) {
      for (int i = 0; i < qdepth; i++) {
        workload_runners.push_back(std::thread(
              nextseq_workload_func, log_impl));
      }
  } else
    assert(0);

  if (runtime) {
    sleep(runtime);
    stop = 1;
  }

  report_runner.join();
  std::for_each(workload_runners.begin(),
      workload_runners.end(), [](std::thread& t) { t.join(); });

  ioctx.close();
  cluster.shutdown();

  return 0;
}
