#ifndef SRC_ZLOG_BENCH_OP_HISTORY_H
#define SRC_ZLOG_BENCH_OP_HISTORY_H
#include <fstream>
#include <iostream>
#include <mutex>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

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

  void dump(int fd) {
    std::lock_guard<std::mutex> l(lock_);
    for (auto& e : history_) {
      dprintf(fd, "%llu %llu\n",
          (unsigned long long)e.start_ns,
          (unsigned long long)e.latency_ns);
    }
    fsync(fd);
  }

  void dump(std::string& output) {
    if (output == "")
      return;

    int fd;
    bool close_fd = false;
    if (output == "-")
      fd = fileno(stdout);
    else {
      fd = open(output.c_str(), O_WRONLY|O_CREAT|O_TRUNC, 0440);
      assert(fd != -1);
      close_fd = true;
    }

    dump(fd);

    if (close_fd)
      close(fd);
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
