#include <atomic>
#include <condition_variable>
#include <mutex>
#include <thread>
#include <signal.h>
#include <time.h>
#include <iostream>
#include <string>
#include <boost/program_options.hpp>
#include "zlog/options.h"
#include "zlog/log.h"
#include "randbytes.h"

namespace po = boost::program_options;

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
  int runtime;
  std::string backend_name;
  std::vector<std::string> backend_options;
  int finisher_threads;

  {
    namespace po = boost::program_options;

    po::options_description opts("Benchmark options");
    opts.add_options()
      ("help", "show help message")
      ("backend-name", po::value<std::string>(&backend_name)->required(), "backend name")
      ("backend-opt", po::value<std::vector<std::string>>(&backend_options)->multitoken(), "backend options")
      ("name", po::value<std::string>(&log_name)->default_value("bench"), "log name")
      ("width", po::value<uint32_t>(&width)->default_value(10), "stripe width")
      ("slots", po::value<uint32_t>(&slots)->default_value(10), "object slots")
      ("size", po::value<size_t>(&entry_size)->default_value(1024), "entry size")
      ("qdepth", po::value<int>(&qdepth)->default_value(1), "queue depth")
      ("runtime", po::value<int>(&runtime)->default_value(0), "runtime")
      ("finisher_threads", po::value<int>(&finisher_threads)->default_value(0), "finisher threads")
      ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, opts), vm);

    if (vm.count("help")) {
      std::cout << opts << std::endl;
      return 1;
    }

    po::notify(vm);
  }

  zlog::Options options;

  // parse backend options from command line arguments
  if (!backend_options.empty()) {
    for (auto option : backend_options) {
      auto pos = option.find(":");
      if (pos == std::string::npos) {
        std::cout << "invalid option " << option << std::endl;
        exit(1);
      }
      auto key = option.substr(0, pos);
      auto val = option.substr(pos+1, option.size()-key.size()-1);
      options.backend_options[key] = val;
    }
  }

  options.backend_name = backend_name;
  options.create_if_missing = true;
  options.error_if_exists = true;
  options.stripe_width = width;
  options.stripe_slots = slots;
  options.max_inflight_ops = qdepth;
  if (finisher_threads > 0) {
    options.finisher_threads = finisher_threads;
  }

  zlog::Log *log;
  int ret = zlog::Log::Open(options, log_name, &log);
  if (ret) {
    std::cerr << "log::open failed: " << strerror(-ret) << std::endl;
    return -1;
  }

  runtime = std::max(runtime, 0);
  signal(SIGINT, sig_handler);
  signal(SIGALRM, sig_handler);
  alarm(runtime);

  std::thread stats_thread(stats_entry);

  zlog::util::rand_data_gen dgen(1ULL << 22, entry_size);
  dgen.generate();

  op_count = 0;
  while (!shutdown) {
    const auto entry_data = std::string(dgen.sample(), entry_size);
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

  log->PrintStats();

  delete log;

  return 0;
}
