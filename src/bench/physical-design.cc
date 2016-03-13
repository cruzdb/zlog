#include <atomic>
#include <condition_variable>
#include <iostream>
#include <boost/program_options.hpp>
#include <signal.h>
#include <rados/librados.hpp>
#include "workload.h"
#include "op_history.h"
#include "common.h"
#include "workloads.h"

namespace po = boost::program_options;

static Workload *workload;
static void sigint_handler(int sig) {
  workload->stop();
}

int main(int argc, char **argv)
{
  std::string pool;
  std::string experiment;

  std::string perf_file;
  size_t entry_size;
  size_t stripe_width;
  int qdepth;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("experiment", po::value<std::string>(&experiment)->required(), "Experiment name")
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

  if (experiment == "map_11") {
  } else if (experiment == "map_n1") {
  } else if (experiment == "bytestream_11") {
  } else if (experiment == "bytestream_n1_write") {
    workload = new ByteStreamN1Write_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history);
  } else if (experiment == "bytestream_n1_append") {
    workload = new ByteStreamN1Append_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history);
  } else {
    std::cerr << "invalid experiment name: " << experiment << std::endl;
    return -1;
  }

  signal(SIGINT, sigint_handler);

  workload->run();

  op_history->dump(perf_file);

  return 0;
}
