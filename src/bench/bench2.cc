#include <atomic>
#include <random>
#include <cassert>
#include <semaphore.h>
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
#include <hdr_histogram.h>
#include <rados/librados.hpp>
#include "include/zlog/backend/ceph.h"
#include "include/zlog/backend/ram.h"
#include "include/zlog/log.h"

namespace po = boost::program_options;

// TODO: reduce data copying in ceph v2
// 1. figure out metrics to collect
// 2. run some tests

class rand_data_gen {
 public:
  rand_data_gen(size_t buf_size, size_t samp_size) :
    buf_size_(buf_size),
    dist_(0, buf_size_ - samp_size - 1)
  {}

  void generate() {
    buf_.reserve(buf_size_);
    std::ifstream ifs("/dev/urandom",
        std::ios::binary | std::ios::in);
    std::copy_n(std::istreambuf_iterator<char>(ifs),
        buf_size_, std::back_inserter(buf_));
  }

  inline const char *sample() {
    assert(!buf_.empty());
    return buf_.c_str() + dist_(gen_);
  }

 private:
  const size_t buf_size_;
  std::string buf_;
  std::default_random_engine gen_;
  std::uniform_int_distribution<size_t> dist_;
};

struct aio_state {
  zlog::AioCompletion *c;
  std::string data;
  uint64_t pos;
  uint64_t start_us;
};

static size_t entry_size;
static sem_t sem;
static std::mutex lock;
static std::condition_variable cond;

static volatile int stop = 0;
static void sigint_handler(int sig) {
  stop = 1;
  sem_post(&sem);
}

static struct hdr_histogram *histogram;
static std::mutex hist_lock;

static std::atomic<uint64_t> ops_done;

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  clock_gettime(clock, &ts);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getus()
{
  return __getns(CLOCK_MONOTONIC) / 1000;
}

static void handle_aio_append_cb(aio_state *io)
{
  auto latency_us = getus() - io->start_us;

  sem_post(&sem);

  // clean-up
  if (io->c->ReturnValue()) {
    std::cout << "error: io retval = "
      << io->c->ReturnValue() << std::endl;
    assert(io->c->ReturnValue() == 0);
    stop = 1;
    exit(1);
  }

  ops_done.fetch_add(1);

  delete io->c;
  io->c = NULL;

  delete io;

  std::lock_guard<std::mutex> lk(hist_lock);
  hdr_record_value(histogram, latency_us);
}

static void handle_aio_read_cb(aio_state *io)
{
  sem_post(&sem);

  // clean-up
  if (io->c->ReturnValue()) {
    std::cout << "error: io retval = "
      << io->c->ReturnValue() << std::endl;
    assert(io->c->ReturnValue() == 0);
    stop = 1;
    exit(1);
  }

  if (io->data.size() != entry_size) {
    std::cerr << "invalid data size read "
      << io->data.size() << std::endl;
    stop = 1;
    exit(1);
  }

  ops_done.fetch_add(1);

  auto latency_us = getus() - io->start_us;
  hdr_record_value(histogram, latency_us);

  delete io->c;
  io->c = NULL;

  delete io;
}

static void reporter(const std::string prefix)
{
  FILE *tpf = nullptr;
  if (!prefix.empty()) {
    std::stringstream fn;
    fn << prefix << ".iops.csv";
    tpf = fopen(fn.str().c_str(), "w");
    fprintf(tpf, "us,iops\n");
  }

  while (true) {
    std::unique_lock<std::mutex> lk(lock);

    auto ops_start = ops_done.load();
    auto start_us = getus();

    cond.wait_for(lk, std::chrono::seconds(1),
        [&] { return stop; });
    if (stop)
      break;

    auto end_us = getus();
    auto ops_end = ops_done.load();

    auto elapsed_us = end_us - start_us;

    auto iops = (double)((ops_end - ops_start) *
        1000000ULL) / (double)elapsed_us;

    std::cout << iops << std::endl;

    if (tpf) {
      fprintf(tpf, "%lu,%f\n", end_us, iops);
    }
  }

  if (tpf) {
    fclose(tpf);
  }

  std::lock_guard<std::mutex> lk(hist_lock);

  if (!prefix.empty()) {
    std::stringstream fn;
    fn << prefix << ".latency.csv";
    FILE *ltf = fopen(fn.str().c_str(), "w");
    hdr_percentiles_print(histogram,
        ltf, 5, 1.0, CSV);
    fclose(ltf);
  }

  hdr_percentiles_print(histogram,
      stdout, 1, 1.0, CLASSIC);
}

int main(int argc, char **argv)
{
  std::string pool;
  std::string logname;
  int runtime;
  int qdepth;
  int width;
  bool ram;
  bool scan;
  std::string prefix;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help,h", "show help message")
    ("logname,l", po::value<std::string>(&logname)->default_value(""), "Log name")
    ("scan", po::bool_switch(&scan)->default_value(false), "scan a log")
    ("runtime,r", po::value<int>(&runtime)->default_value(0), "runtime")
    ("pool,p", po::value<std::string>(&pool)->required(), "Pool name")
    ("width,w", po::value<int>(&width)->default_value(10), "stripe width")
    ("size,s", po::value<size_t>(&entry_size)->default_value(1024), "entry size")
    ("qdepth,q", po::value<int>(&qdepth)->default_value(1), "aio queue depth")
    ("ram", po::bool_switch(&ram)->default_value(false), "ram backend")
    ("prefix", po::value<std::string>(&prefix)->default_value(""), "name prefix")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, opts), vm);

  if (vm.count("help")) {
    std::cout << opts << std::endl;
    return 1;
  }

  po::notify(vm);

  if (logname.empty()) {
    std::stringstream ss;
    auto uuid = boost::uuids::random_generator()();
    ss << uuid << ".log";
    logname = ss.str();
  }

  // only used for ceph backend
  librados::Rados cluster;
  librados::IoCtx ioctx;

  std::unique_ptr<zlog::Backend> backend;
  if (ram) {
    backend = std::unique_ptr<zlog::storage::ram::RAMBackend>(
        new zlog::storage::ram::RAMBackend());
  } else {
    // connect to rados
    cluster.init(NULL);
    cluster.conf_read_file(NULL);
    int ret = cluster.connect();
    assert(ret == 0);
    (void)ret;

    // open pool i/o context
    ret = cluster.ioctx_create(pool.c_str(), ioctx);
    assert(ret == 0);

    backend = std::unique_ptr<zlog::Backend>(
        new zlog::storage::ceph::CephBackend(&ioctx));
  }

  zlog::Options options;
  zlog::Log *log;

  if (scan) {
    int ret = zlog::Log::OpenWithBackend(options,
        std::move(backend), logname, &log);
    if (ret) {
      std::cerr << "failed to open log " << ret << std::endl;
      exit(1);
    }
  } else {
    int ret = zlog::Log::CreateWithBackend(options,
        std::move(backend), logname, &log);
    if (ret) {
      std::cerr << "failed to create log " << ret << std::endl;
      exit(1);
    }
  }

  signal(SIGINT, sigint_handler);
  signal(SIGALRM, sigint_handler);
  alarm(runtime);

  rand_data_gen dgen(1ULL << 22, entry_size);
  dgen.generate();

  hdr_init(1, INT64_C(50000000), 3, &histogram);

  ops_done = 0;
  std::thread reporter_thread(reporter, prefix);

  sem_init(&sem, 0, qdepth);

  if (scan) {
    uint64_t tail;
    int ret = log->CheckTail(&tail);
    if (ret) {
      std::cerr << "check tail failed" << std::endl;
      stop = 1;
      exit(1);
    }
    for (uint64_t pos = 0; pos < tail; pos++) {
      sem_wait(&sem);

      if (stop)
        break;

      aio_state *io = new aio_state;
      io->c = zlog::Log::aio_create_completion(
          std::bind(handle_aio_read_cb, io));
      io->start_us = getus();

      int ret = log->AioRead(pos, io->c, &io->data);
      if (ret) {
        std::cerr << "aio read failed " << ret << std::endl;
        exit(1);
      }
    }
  } else {
    for (;;) {
      sem_wait(&sem);

      if (stop)
        break;

      aio_state *io = new aio_state;
      io->c = zlog::Log::aio_create_completion(
          std::bind(handle_aio_append_cb, io));
      io->start_us = getus();

      int ret = log->AioAppend(io->c,
          zlog::Slice(dgen.sample(), entry_size), &io->pos);
      if (ret) {
        std::cerr << "aio append failed " << ret << std::endl;
        exit(1);
      }
    }
  }

  // wait for I/Os to complete
  while (true) {
    int val;
    sem_getvalue(&sem, &val);
    if (val == qdepth)
      break;
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
  }

  stop = 1;
  cond.notify_all();
  reporter_thread.join();
  hdr_close(histogram);

  if (!ram) {
    ioctx.aio_flush();
    ioctx.close();
    cluster.shutdown();
  }

  return 0;
}
