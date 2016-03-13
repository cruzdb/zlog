#ifndef ZLOG_SRC_BENCH_COMMON_H
#define ZLOG_SRC_BENCH_COMMON_H
#include <mutex>
#include <iostream>
#include <fstream>

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

class OpHistory {
 public:
  OpHistory() {}
  OpHistory(size_t capacity) {
    history_.reserve(capacity);
  }

  void add_latency(uint64_t start, uint64_t latency) {
    std::lock_guard<std::mutex> l(lock_);
    history_.emplace_back(op{start, latency});
  }

  void dump(std::ostream& os) {
    std::lock_guard<std::mutex> l(lock_);
    for (auto& e : history_) {
      os << e.start_ns << " " << e.latency_ns << std::endl;
    }
    os.flush();
  }

  void dump(std::string& output) {
    if (output == "")
      return;
    std::ofstream ofs;
    if (output != "-")
      ofs.open(output, std::ios::out|std::ios::trunc);
    std::ostream& os = output == "-" ? std::cout : ofs;
    dump(os);
  }

 private:
  struct op {
    uint64_t start_ns;
    uint64_t latency_ns;
  };

  std::mutex lock_;
  std::vector<op> history_;
};

#endif
