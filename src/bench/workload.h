#ifndef SRC_ZLOG_BENCH_WORKLOAD_H
#define SRC_ZLOG_BENCH_WORKLOAD_H
#include "op_history.h"
#include "common.h"

/*
 * Workload Generator
 */
class Workload {
 public:
  Workload(OpHistory *op_history, int qdepth, size_t entry_size,
      std::string& prefix) :
    seq(0), entry_size_(entry_size), outstanding_ios(0),
    op_history_(op_history), qdepth_(qdepth), stop_(0),
    prefix_(prefix)
  {
    if (prefix_ != "")
      prefix_ = prefix_ + ".";
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

        // TODO: select from pool
        char data[entry_size_];
        ceph::bufferlist bl;
        bl.append(data, entry_size_);

        // create operation
        gen_op(io->rc, &io->submitted_ns, bl);

        outstanding_ios++;
        seq++;
      }

      io_cond.wait(lock, [&]{ return outstanding_ios < qdepth_; });

      if (stop_)
        break;
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
    delete io;

    // record
    io->workload->op_history_->add_latency(submitted_ns, latency_ns);
  }

  std::atomic_ullong outstanding_ios;
  std::condition_variable io_cond;
  std::mutex io_lock;
  OpHistory *op_history_;
  int qdepth_;
  volatile int stop_;
};

#endif
