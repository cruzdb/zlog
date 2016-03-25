#ifndef SRC_ZLOG_BENCH_OP_HISTORY_H
#define SRC_ZLOG_BENCH_OP_HISTORY_H
#include <fstream>
#include <iostream>
#include <mutex>
#include <thread>
#include <condition_variable>
#include <vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

/*
 *
 */
class OpHistory {
 public:
  OpHistory(size_t capacity, std::string& output) :
    capacity_(capacity), output_(output)
  {
    history_.reserve(capacity);
    flusher_ = std::thread(&OpHistory::flush, this);
    flush_level_ = capacity / 2;
    stop_ = false;
    entries_written_ = 0;
  }

  void add_latency(uint64_t start, uint64_t latency) {
    std::lock_guard<std::mutex> l(lock_);
    history_.emplace_back(op{start, latency});
    if (history_.size() > flush_level_)
      flush_cond_.notify_one();
  }

  void add_iops(uint64_t timestamp, unsigned iops) {
    std::lock_guard<std::mutex> l(lock_);
    history_.emplace_back(op{timestamp, iops});
    if (history_.size() > flush_level_)
      flush_cond_.notify_one();
  }

  void stop() {
    lock_.lock();
    stop_ = true;
    flush_cond_.notify_one();
    lock_.unlock();
    flusher_.join();
  }

 private:
  /*
   * This tracks IOPS too in which case start_ns is a timestamp, and
   * latency_ns is the number of iops in the previous period.
   */
  struct op {
    uint64_t start_ns;
    uint64_t latency_ns;
  };

  void flush() {
    // open the output stream
    int fd;
    bool close_fd = false;
    if (output_ == "-")
      fd = fileno(stdout);
    else {
      fd = open(output_.c_str(), O_WRONLY|O_CREAT|O_TRUNC, 0440);
      assert(fd != -1);
      close_fd = true;
    }

    std::vector<op> tmp_history;

    std::unique_lock<std::mutex> lock(lock_);

    for (;;) {
      // wait for something to do
      flush_cond_.wait(lock,
          [&]{ return ((history_.size() > flush_level_) || stop_); });

      // grab the current history and replace it
      // with an empty buffer for operations.
      tmp_history.clear();
      tmp_history.reserve(capacity_);
      history_.swap(tmp_history);

      lock.unlock();

      for (auto& e : tmp_history) {
        dprintf(fd, "%llu %llu\n",
            (unsigned long long)e.start_ns,
            (unsigned long long)e.latency_ns);
        entries_written_++;
      }

      lock.lock();

      if (stop_ && history_.empty())
        break;
    }

    fsync(fd);

    if (close_fd)
      close(fd);

    std::cout << "wrote " << entries_written_ << " entries" << std::endl;
  }

  size_t capacity_;
  size_t flush_level_;
  std::thread flusher_;
  std::string output_;
  bool stop_;
  size_t entries_written_;

  std::vector<op> history_;

  std::mutex lock_;
  std::condition_variable flush_cond_;
};

#endif
