#include <atomic>
#include <condition_variable>
#include <memory>
#include <mutex>
#include <random>
#include <thread>
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <boost/program_options.hpp>
#include "zlog/backend/ram.h"
#include "zlog/options.h"
#include "zlog/log.h"

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

static std::atomic<bool> shutdown;
static std::atomic<uint64_t> op_count;

static std::mutex lock;
static std::condition_variable cond;

static void sig_handler(int sig)
{
  shutdown = true;
}

static void stats_entry()
{
  while (true) {
    auto start_ops_count = op_count.load();
    auto start_us = getus();

    std::unique_lock<std::mutex> lk(lock);
    cond.wait_for(lk, std::chrono::seconds(1),
        [&] { return shutdown.load(); });
    if (shutdown) {
      break;
    }

    auto end_us = getus();
    auto end_ops_count = op_count.load();

    auto elapsed_us = end_us - start_us;

    auto iops = (double)((end_ops_count - start_ops_count) *
        1000000ULL) / (double)elapsed_us;

    std::cout << iops << std::endl;
  }
}

int main(int argc, char **argv)
{
  std::string log_name;
  uint32_t width;
  uint32_t slots;
  size_t entry_size;
  int qdepth;
  bool verify;
  int runtime;
  std::string backend;
  std::string pool;
  std::string db_path;
  bool blackhole;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help", "show help message")
    ("name", po::value<std::string>(&log_name)->default_value("bench"), "log name")
    ("width", po::value<uint32_t>(&width)->default_value(10), "stripe width")
    ("slots", po::value<uint32_t>(&slots)->default_value(10), "object slots")
    ("size", po::value<size_t>(&entry_size)->default_value(1024), "entry size")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "queue depth")
    ("verify", po::bool_switch(&verify), "verify writes")
    ("runtime", po::value<int>(&runtime)->default_value(0), "runtime")

    ("backend", po::value<std::string>(&backend)->required(), "backend")
    ("pool", po::value<std::string>(&pool)->default_value("zlog"), "pool (ceph)")
    ("db-path", po::value<std::string>(&db_path)->default_value("/tmp/zlog.bench.db"), "db path (lmdb)")
    ("blackhole", po::bool_switch(&blackhole), "black hole (ram)")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, opts), vm);

  if (vm.count("help")) {
    std::cout << opts << std::endl;
    return 1;
  }

  po::notify(vm);

  runtime = std::max(runtime, 0);

  zlog::Options options;
  options.backend_name = backend;

  if (backend == "ceph") {
    options.backend_options["pool"] = pool;
    // zero-length string here causes default path search
    options.backend_options["conf_file"] = "";
  }

  if (backend == "lmdb") {
    options.backend_options["path"] = db_path;
  }

  if (backend == "ram") {
    if (blackhole) {
      options.backend_options["blackhole"] = "true";
    }
  }

  options.create_if_missing = true;
  options.error_if_exists = true;

  options.stripe_width = width;
  options.stripe_slots = slots;
  options.max_inflight_ops = qdepth;

  zlog::Log *log;
  int ret = zlog::Log::Open(options, log_name, &log);
  if (ret) {
    std::cerr << "log::open failed: " << strerror(-ret) << std::endl;
    return -1;
  }

  signal(SIGINT, sig_handler);
  signal(SIGALRM, sig_handler);
  alarm(runtime);

  rand_data_gen dgen(1ULL << 22, entry_size);
  dgen.generate();

  // TODO: by always logging the same entry data we may trigger low-level
  // compression to take affect, if such a thing exists. something to be aware
  // of and watch out for.
  const auto entry_data = std::string(dgen.sample(), entry_size);

  std::thread stats_thread(stats_entry);

  op_count = 0;
  while (!shutdown) {
    int ret = log->appendAsync(entry_data, [&](int ret, uint64_t pos) {
      if (ret && ret != -ESHUTDOWN) {
        std::cerr << "appendAsync cb failed: " << strerror(-ret) << std::endl;
        assert(0);
        return;
      }
      op_count++;
    });
    if (ret) {
      std::cerr << "appendAsync failed: " << strerror(-ret) << std::endl;
      assert(0);
      break;
    }
  }

  shutdown = true;
  cond.notify_one();
  stats_thread.join();

  if (verify) {
    uint64_t tail;
    auto ret = log->CheckTail(&tail);
    if (ret) {
      std::cerr << "checktail failed: " << strerror(-ret) << std::endl;
    } else {
      for (uint64_t pos = 0; pos < tail; pos++) {
        std::string data;
        ret = log->Read(pos, &data);
        if (ret) {
          std::cerr << "read failed at pos " << pos << ": " << strerror(-ret) << std::endl;
        } else if (data != entry_data) {
          std::cerr << "verify failed at pos " << pos << std::endl;
          assert(0);
        }
      }
    }
  }

  delete log;

  return 0;
}
