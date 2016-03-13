#include <atomic>
#include <condition_variable>
#include <iostream>
#include <boost/program_options.hpp>
#include <signal.h>
#include <rados/librados.hpp>
#include "workload.h"
#include "op_history.h"
#include "common.h"

namespace po = boost::program_options;

static Workload *workload_ptr;
static void sigint_handler(int sig) {
  workload_ptr->stop();
}

class PayloadAppendWorkload : public Workload {
 public:
  PayloadAppendWorkload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history) :
    Workload(op_history, qdepth),
    ioctx_(ioctx),
    stripe_width_(stripe_width),
    entry_size_(entry_size)
  {}

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns) {
    // target object
    std::stringstream oid;
    size_t stripe_offset = seq % stripe_width_;
    oid << "log." << stripe_offset;
    
    // data
    char data[entry_size_];
    ceph::bufferlist bl;
    bl.append(data, entry_size_);

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_append(oid.str(), rc, bl, bl.length());
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entry_size_;
};

int main(int argc, char **argv)
{
  std::string pool;
  std::string perf_file;
  size_t entry_size;
  size_t stripe_width;
  int qdepth;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("stripe_width", po::value<size_t>(&stripe_width)->required(), "Stripe width")
    ("entry_size", po::value<size_t>(&entry_size)->required(), "Entry size")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
    ("perf_file", po::value<std::string>(&perf_file)->default_value(""), "Perf output")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  // connect to rados
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open target pool i/o context
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  OpHistory *op_history = new OpHistory(2000000);

  PayloadAppendWorkload workload(&ioctx, stripe_width,
      entry_size, qdepth, op_history);

  workload_ptr = &workload;
  signal(SIGINT, sigint_handler);

  workload.run();

  op_history->dump(perf_file);

  return 0;
}
