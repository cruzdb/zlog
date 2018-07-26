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
#include <boost/crc.hpp>
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
#include "include/zlog/backend/lmdb.h"
#include "include/zlog/log.h"

namespace po = boost::program_options;

class rand_data_gen {
 public:
  rand_data_gen(size_t buf_size, size_t samp_size) :
    buf_size_(buf_size),
    dist_(0, buf_size_ - samp_size - 1)
  {}

  void generate() {
   std::uniform_int_distribution<uint64_t> d(
        std::numeric_limits<uint64_t>::min(),
        std::numeric_limits<uint64_t>::max());
    buf_.reserve(buf_size_);
    while (buf_.size() < buf_size_) {
      uint64_t val = d(gen_);
      buf_.append((const char *)&val, sizeof(val));
    }
    if (buf_.size() > buf_size_)
      buf_.resize(buf_size_);
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
  uint32_t crc32;
};

static size_t entry_size;

static bool verify_writes;
static std::string checksum_file;
static std::unordered_map<uint64_t, uint32_t> checksums;

static sem_t sem;
static std::mutex lock;
static std::condition_variable cond;

static volatile int stop = 0;
static void sig_handler(int sig) {
  if (sig == SIGALRM) {
    std::cout << "runtime exceeded" << std::endl;
  }
  stop = 1;
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

static uint32_t crc32(const char *data, size_t size)
{
  boost::crc_32_type result;
  result.process_bytes(data, size);
  return result.checksum();
}

static void handle_aio_append_cb(aio_state *io)
{
  auto latency_us = getus() - io->start_us;
  ops_done.fetch_add(1);

  sem_post(&sem);

  if (io->c->ReturnValue()) {
    std::cout << "error: io retval = "
      << io->c->ReturnValue() << std::endl;
    assert(io->c->ReturnValue() == 0);
    stop = 1;
    exit(1);
  }

  if (verify_writes) {
    checksums.emplace(io->pos, io->crc32);
  }

  delete io->c;
  delete io;

  std::lock_guard<std::mutex> lk(hist_lock);
  hdr_record_value(histogram, latency_us);
}

static void handle_aio_read_cb(aio_state *io)
{
  auto latency_us = getus() - io->start_us;
  ops_done.fetch_add(1);

  sem_post(&sem);

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

  if (verify_writes) {
    auto checksum = crc32(io->data.c_str(), io->data.size());
    auto expected = checksums.at(io->pos);
    if (checksum != expected) {
      std::cerr << "checksum error at pos " << io->pos << std::endl;
      exit(1);
    }
  }

  delete io->c;
  delete io;

  std::lock_guard<std::mutex> lk(hist_lock);
  hdr_record_value(histogram, latency_us);
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
  std::string backend_type;
  bool scan;
  std::string prefix;
  double max_gbs;
  int entries_per_object;
  int max_entry_size;
  int cache_size;
  int cache_eviction;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help,h", "show help message")
    ("logname,l", po::value<std::string>(&logname)->default_value(""), "Log name")
    ("scan", po::bool_switch(&scan)->default_value(false), "scan a log")
    ("runtime,r", po::value<int>(&runtime)->default_value(0), "runtime")
    ("pool,p", po::value<std::string>(&pool)->required(), "Pool name")
    ("width,w", po::value<int>(&width)->default_value(-1), "stripe width")
    ("epo", po::value<int>(&entries_per_object)->default_value(-1), "entries per object")
    ("size,s", po::value<size_t>(&entry_size)->default_value(1024), "entry size")
    ("qdepth,q", po::value<int>(&qdepth)->default_value(1), "aio queue depth")
    ("backend,b", po::value<std::string>(&backend_type)->default_value("ram"), "backend")
    ("prefix", po::value<std::string>(&prefix)->default_value(""), "name prefix")
    ("verify", po::value<std::string>(&checksum_file)->default_value(""), "verify writes data")
    ("max_entry_size", po::value<int>(&max_entry_size)->default_value(-1), "max entry size")
    ("max_gbs", po::value<double>(&max_gbs)->default_value(0.0), "max gbs to write")
    ("cache_size", po::value<int>(&cache_size)->default_value(0), "number of cache entries")
    ("cache_eviction", po::value<int>(&cache_eviction)->default_value(0), "cache eviction policy 0:LRU 1:ARC")
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

  if (!checksum_file.empty()) {
    verify_writes = true;
    if (scan) {
      std::fstream in(checksum_file, std::ios_base::in);
      uint64_t pos;
      uint32_t crc32;
      while (in >> pos) {
        in >> crc32;
        checksums.emplace(pos, crc32);
      }
    }
  }

  if (runtime == 0 && max_gbs == 0.0) {
    runtime = 30;
  }

  const uint64_t max_bytes = (1ULL << 30) * max_gbs;

  // only used for ceph backend
  librados::Rados cluster;
  librados::IoCtx ioctx;

  std::unique_ptr<zlog::Backend> backend;

  std::cout << "Using backend: " << backend_type << std::endl;

  if (!backend_type.compare("ram")) {
    backend = std::unique_ptr<zlog::storage::ram::RAMBackend>(
      new zlog::storage::ram::RAMBackend());
      
  }else if (!backend_type.compare("ceph")) {

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
  }else if (!backend_type.compare("lmdb")) {
    backend = std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
      new zlog::storage::lmdb::LMDBBackend());
    auto raw_ptr = backend.get();
    ((zlog::storage::lmdb::LMDBBackend*)raw_ptr)->Init("/tmp/zlog.tmp.db");
  }else{
    std::cout << "invalid backend" << std::endl;
    exit(1);
  } 
  zlog::Options options;
  if (width > 0)
    options.width = width;

  if (entries_per_object > 0)
    options.entries_per_object = entries_per_object;

  if (max_entry_size <= 0)
    options.max_entry_size = entry_size;
  
  if (cache_size >= 0){
    options.cache_size = cache_size;
  }

  options.eviction = (zlog::Eviction::Eviction_Policy)cache_eviction;

  auto stats = zlog::CreateCacheStatistics();
  options.statistics = stats;

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

  signal(SIGINT, sig_handler);
  signal(SIGALRM, sig_handler);
  if(!scan)
    alarm(runtime);

  rand_data_gen dgen(1ULL << 22, entry_size);
  dgen.generate();

  hdr_init(1,
      INT64_C(30000000),
      3, &histogram);

  ops_done = 0;
  std::thread reporter_thread(reporter, prefix);

  sem_init(&sem, 0, qdepth);

  if (scan) {

    uint64_t tail;
    int ret = log->CheckTail(&tail);

    std::default_random_engine gen;
    std::binomial_distribution<size_t> read_dist((double)tail/2.0);
    uint64_t read_ops = tail * 3;
    

    if (ret) {
      std::cerr << "check tail failed" << std::endl;
      stop = 1;
      exit(1);
    }
    for (uint64_t i = 0; i < read_ops; i++) {
      sem_wait(&sem);
      if (stop)
        break;

      int pos = read_dist(gen);
      aio_state *io = new aio_state;
      io->c = zlog::Log::aio_create_completion(
          std::bind(handle_aio_read_cb, io));
      io->start_us = getus();
      io->pos = pos;

      int ret = log->AioRead(io->pos, io->c, &io->data);
      if (ret) {
        std::cerr << "aio read failed " << ret << std::endl;
        exit(1);
      }
    }
  } else {
    uint64_t bytes_written = 0;
    for (;;) {
      sem_wait(&sem);
      if (stop || (max_bytes > 0 && bytes_written >= max_bytes)) {
        if (max_bytes > 0 && bytes_written >= max_bytes) {
          std::cout << "max bytes written reached" << std::endl;
        }
        sem_post(&sem);
        break;
      }

      aio_state *io = new aio_state;
      io->c = zlog::Log::aio_create_completion(
          std::bind(handle_aio_append_cb, io));
      io->start_us = getus();

      auto data = dgen.sample();

      if (verify_writes) {
        io->crc32 = crc32(data, entry_size);
      }

      int ret = log->AioAppend(io->c,
          zlog::Slice(data, entry_size), &io->pos);
      bytes_written += entry_size;

      if (ret) {
        std::cerr << "aio append failed " << ret << std::endl;
        exit(1);
      }
    }
  }

  while (true) {
    int val;
    sem_getvalue(&sem, &val);
    if (val == qdepth)
      break;
    std::this_thread::sleep_for(
        std::chrono::milliseconds(100));
  }

  stop = 1;
  cond.notify_all();
  reporter_thread.join();
  hdr_close(histogram);

  std::cout << "CACHE STATISTICS:" << std::endl << options.statistics->ToString(); 


  if (!checksum_file.empty()) {
    std::fstream out(checksum_file, std::ios_base::out | std::ios_base::trunc);
    for (auto it = checksums.begin(); it != checksums.end();) {
      out << it->first << std::endl << it->second;
      if (++it != checksums.end())
        out << std::endl;
    }
  }

  if (!backend_type.compare("ceph")) {
    ioctx.aio_flush();
    ioctx.close();
    cluster.shutdown();
  }

  delete(log);

  return 0;
}
