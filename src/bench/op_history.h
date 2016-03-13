#ifndef SRC_ZLOG_BENCH_OP_HISTORY_H
#define SRC_ZLOG_BENCH_OP_HISTORY_H
#include <fstream>
#include <iostream>
#include <mutex>
#include <vector>

/*
 *
 */
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
