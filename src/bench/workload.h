#ifndef SRC_ZLOG_BENCH_WORKLOAD_H
#define SRC_ZLOG_BENCH_WORKLOAD_H
#include <random>
#include <iterator>
#include "op_history.h"
#include "common.h"

/*
 * Workload Generator
 */
class Workload {
 public:
  Workload(OpHistory *op_history, int qdepth, size_t entry_size,
      std::string& prefix, int tp_sec) :
    seq(0), entry_size_(entry_size), outstanding_ios(0),
    op_history_(op_history), qdepth_(qdepth), stop_(0),
    prefix_(prefix), tp_sec_(tp_sec)
  {
    if (prefix_ != "")
      prefix_ = prefix_ + ".";

    // create random data to use for payloads
    rand_buf_size_ = 1ULL<<23;
    rand_buf_.reserve(rand_buf_size_);
    std::ifstream ifs("/dev/urandom", std::ios::binary | std::ios::in);
    std::copy_n(std::istreambuf_iterator<char>(ifs),
        rand_buf_size_, std::back_inserter(rand_buf_));
    rand_buf_raw_ = rand_buf_.c_str();

    rand_dist = std::uniform_int_distribution<int>(0,
        rand_buf_size_ - entry_size_ - 1);

    stats_thread_ = std::thread(&Workload::print_stats, this);
  }

  virtual void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) = 0;

  void run() {
    std::unique_lock<std::mutex> lock(io_lock);
    for (;;) {
      while (outstanding_ios < qdepth_) {
        // create context to track the io
        aio_state *io = new aio_state;
        io->workload = this;
        io->rc = librados::Rados::aio_create_completion(io, NULL, handle_io_cb);
        assert(io->rc);

        // select random slice of random byte buffer
        size_t buf_offset = rand_dist(generator);
        ceph::bufferlist bl;
        bl.append(rand_buf_raw_ + buf_offset, entry_size_);

        // create operation
        gen_op(io->rc, &io->submitted_ns, bl);

        outstanding_ios++;
        seq++;
      }

      io_cond.wait(lock, [&]{ return outstanding_ios < qdepth_; });

      if (stop_)
        break;
    }

    while (1) {
      if (outstanding_ios == 0)
        break;
      std::cout << "draining ios: " << outstanding_ios << " remaining" << std::endl;
      sleep(1);
    }
  }

  void stop() {
    std::cout << "Stopping workload..." << std::endl;
    stop_ = 1;
  }

 protected:
  size_t entry_size_;
  std::atomic_ullong seq;
  std::string prefix_;

 private:
  struct aio_state {
    librados::AioCompletion *rc;
    uint64_t submitted_ns;
    Workload *workload;
  };

  static void handle_io_cb(librados::completion_t cb, void *arg)
  {
    aio_state *io = (aio_state*)arg;

    // timing
    uint64_t submitted_ns = io->submitted_ns;
    uint64_t latency_ns = getns() - submitted_ns;

    // clean-up
    io->workload->outstanding_ios--;
    assert(io->rc->get_return_value() == 0);
    io->rc->release();
    io->workload->io_cond.notify_one();

    // record the latency of this IO unless we are tracing throughput or
    // tracing isn't enabled.
    if (io->workload->tp_sec_ == 0 && io->workload->op_history_)
      io->workload->op_history_->add_latency(submitted_ns, latency_ns);

    io->workload->ios_completed_++;

    delete io;
  }

  void print_stats() {

    sleep(2);

    int period = tp_sec_;
    bool track_iops = period > 0;
    if (!track_iops)
      period = 2;

    uint64_t expr_start_ns = getns();

    ios_completed_ = 0;
    uint64_t start_ns = getns();

    while (!stop_) {

      // length of time to accumulate iops stats
      sleep(period);

      uint64_t period_ios_completed = ios_completed_.exchange(0);
      uint64_t end_ns = getns();
      uint64_t dur_ns = end_ns - start_ns;
      start_ns = end_ns;

      // completed ios in prev period
      double iops = (double)(period_ios_completed * 1000000000ULL) / (double)dur_ns;

      if (track_iops && op_history_)
        op_history_->add_iops(end_ns, (int)iops);

      uint64_t elapsed_sec = (end_ns - expr_start_ns) / 1000000000ULL;
      std::cout << elapsed_sec << "s: " << "rate=" << (int)iops << " iops" << std::endl;
    }
  }

  std::atomic_ullong outstanding_ios;
  std::condition_variable io_cond;
  std::mutex io_lock;
  OpHistory *op_history_;
  int qdepth_;
  volatile int stop_;
  std::string rand_buf_;
  size_t rand_buf_size_;
  const char *rand_buf_raw_;
  std::default_random_engine generator;
  std::uniform_int_distribution<int> rand_dist;
  int tp_sec_;

  std::thread stats_thread_;
  std::atomic_ullong ios_completed_;
};

#endif
