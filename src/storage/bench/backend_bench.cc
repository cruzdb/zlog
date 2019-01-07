#include <atomic>
#include <condition_variable>
#include <memory>
#include <mutex>
#include <random>
#include <sstream>
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

static std::atomic<uint64_t> seq;

static bool verify = false;
static std::unordered_map<uint64_t, std::string> record;

static std::mutex lock;
static std::condition_variable cond;

static void sig_handler(int sig)
{
  shutdown = true;
}

static void io_entry(std::shared_ptr<zlog::Backend> backend,
    const std::vector<std::vector<std::string>>& objects,
    uint64_t width, uint64_t slots, size_t entry_size,
    uint64_t max_pos, rand_data_gen *gen)
{
  assert(!objects.empty());
  assert(objects[0].size() == width);

  const auto slots_per_row = width * slots;

  while (true) {
    if (shutdown) {
      break;
    }

    auto pos = seq.fetch_add(1);
    assert(pos < max_pos);

    auto row = pos / slots_per_row;
    auto col = pos % width;

    std::string data;
    data.append(gen->sample(), entry_size);

    int ret = backend->Write(objects[row][col], data, 1, pos);
    if (ret) {
      std::cerr << "write error: " << strerror(-ret) << std::endl;
      assert(0);
    }

    if (verify) {
      record.emplace(pos, data);
    }

    op_count++;
  }
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
  std::string prefix;
  uint32_t width;
  uint32_t slots;
  size_t entry_size;
  int qdepth;
  int runtime;
  std::string backend_name;
  std::string pool;
  std::string db_path;
  uint64_t max_pos;
  ssize_t omap_max_size;

  po::options_description opts("Benchmark options");
  opts.add_options()
    ("help,h", "show help message")
    ("prefix", po::value<std::string>(&prefix)->default_value("backend_bench"), "prefix")
    ("width", po::value<uint32_t>(&width)->default_value(10), "stripe width")
    ("slots", po::value<uint32_t>(&slots)->default_value(10), "object slots")
    ("size", po::value<size_t>(&entry_size)->default_value(1024), "entry size")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "queue depth")
    ("runtime", po::value<int>(&runtime)->default_value(0), "runtime")
    ("maxpos", po::value<uint64_t>(&max_pos)->default_value(1000000), "max pos")
    ("verify", po::bool_switch(&verify), "verify")

    ("backend", po::value<std::string>(&backend_name)->required(), "backend")
    ("pool", po::value<std::string>(&pool)->default_value("zlog"), "pool (ceph)")
    ("db-path", po::value<std::string>(&db_path)->default_value("/tmp/zlog.bench.db"), "db path (lmdb)")
    ("omap-max-size", po::value<ssize_t>(&omap_max_size)->default_value(-1), "omap max size (ceph)")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, opts), vm);

  if (vm.count("help")) {
    std::cout << opts << std::endl;
    return 1;
  }

  po::notify(vm);

  assert(qdepth > 0);
  runtime = std::max(runtime, 0);

  zlog::Options options;
  options.backend_name = backend_name;

  if (backend_name == "ceph") {
    options.backend_options["pool"] = pool;
    // zero-length string here causes default path search
    options.backend_options["conf_file"] = "";
    if (omap_max_size >= 0) {
      std::stringstream ss;
      ss << omap_max_size;
      options.backend_options["omap_max_size"] = ss.str();
    }
  } else if (backend_name == "lmdb") {
    options.backend_options["path"] = db_path;
  }

  std::shared_ptr<zlog::Backend> backend;
  int ret = zlog::Backend::Load(options.backend_name,
      options.backend_options, backend);
  if (ret) {
    std::cerr << "backend::load " << ret << std::endl;
    return ret;
  }

  signal(SIGINT, sig_handler);
  signal(SIGALRM, sig_handler);

  rand_data_gen dgen(1ULL << 22, entry_size);
  dgen.generate();

  shutdown = false;
  seq = 0;

  const auto slots_per_row = width * slots;
  const auto num_rows = max_pos / slots_per_row;
  std::vector<std::vector<std::string>> objects;
  for (auto row = 0u; row < num_rows; row++) {
    std::vector<std::string> tmp;
    for (auto col = 0u; col < width; col++) {
      std::stringstream ss;
      ss << prefix << "." << row << "." << col;
      auto oid = ss.str();
      int ret = backend->Seal(oid, 1);
      if (ret) {
        std::cerr << "seal error: " << strerror(-ret) << std::endl;
        assert(0);
      }
      tmp.push_back(ss.str());
    }
    if (shutdown) {
      break;
    }
    objects.push_back(tmp);
  }

  std::vector<std::thread> io_threads;
  for (int i = 0; i < qdepth; i++) {
    io_threads.emplace_back(std::thread(io_entry, backend, objects,
          width, slots, entry_size, max_pos, &dgen));
  }

  std::thread stats_thread(stats_entry);

  alarm(runtime);

  stats_thread.join();
  for (auto& t : io_threads) {
    t.join();
  }

  if (verify) {
    const auto slots_per_row = width * slots;
    for (auto it : record) {
      auto pos = it.first;
      auto row = pos / slots_per_row;
      auto col = pos % width;
      auto oid = objects[row][col];
      std::string data;
      int ret = backend->Read(oid, 1, pos, &data);
      assert(ret == 0);
      assert(it.second == data);
      std::cout << "verify " << pos << std::endl;
    }
  }

  return 0;
}
