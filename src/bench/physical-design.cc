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
  std::string prefix;
  int tp_sec;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("experiment", po::value<std::string>(&experiment)->required(), "Experiment name")
    ("stripe_width", po::value<size_t>(&stripe_width)->default_value(0), "Stripe width")
    ("entry_size", po::value<size_t>(&entry_size)->required(), "Entry size")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
    ("prefix", po::value<std::string>(&prefix)->default_value(""), "Rados prefix")
    ("tp",        po::value<int>(&tp_sec)->default_value(0), "Throughput tracing")
    ("perf_file", po::value<std::string>(&perf_file)->default_value(""), "Perf output")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  if (qdepth <= 0) {
    std::cerr << "invalid qdepth " << qdepth << std::endl;
    return -1;
  }

  if (entry_size <= 0 || entry_size > (1ULL<<25)) {
    std::cerr << "invalid entry_size " << entry_size << std::endl;
    return -1;
  }

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

  OpHistory *op_history = NULL;
  if (perf_file != "")
    op_history = new OpHistory(2000000, perf_file);

  if (experiment == "map_11") {

    if (stripe_width != 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    workload = new Map11_Workload(&ioctx, entry_size,
        qdepth, op_history, prefix, tp_sec);

  } else if (experiment == "map_n1") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    workload = new MapN1_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec);

  } else if (experiment == "bytestream_11") {

    if (stripe_width != 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    workload = new ByteStream11_Workload(&ioctx, entry_size,
        qdepth, op_history, prefix, tp_sec);

  } else if (experiment == "bytestream_n1_write") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    workload = new ByteStreamN1Write_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec);

  } else if (experiment == "bytestream_n1_append") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    workload = new ByteStreamN1Append_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec);

  } else {
    std::cerr << "invalid experiment name: " << experiment << std::endl;
    return -1;
  }

  signal(SIGINT, sigint_handler);

  workload->run();

  if (op_history)
    op_history->stop();

  return 0;
}
