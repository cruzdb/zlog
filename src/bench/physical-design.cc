#include <atomic>
#include <condition_variable>
#include <iostream>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "workload.h"
#include "op_history.h"
#include "common.h"
#include "workloads.h"

namespace po = boost::program_options;

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
  int runtime;

  std::string interface_name;
  StorageInterface interface;

  bool use_stripe_groups;

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
    ("runtime", po::value<int>(&runtime)->default_value(30), "Runtime (sec)")
    ("interface", po::value<std::string>(&interface_name)->default_value("vanilla"), "Storage interface")
    ("use_stripe_group", po::value<bool>(&use_stripe_groups)->default_value(false), "Use stripe groups")
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

  if (interface_name == "vanilla") {
    interface = VANILLA;
  } else if (interface_name == "cls_no_index") {
    interface = CLS_NO_INDEX;
  } else if (interface_name == "cls_check_epoch") {
    interface = CLS_CHECK_EPOCH;
  } else if (interface_name == "cls_full") {
    interface = CLS_FULL;
  } else {
    std::cerr << "invalid storage interface " << interface_name << std::endl;
    return -1;
  }

  std::cout << "using storage interface: " << interface_name << std::endl;

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

  Workload *workload;

  /*
   * =================== map/11 ======================
   */
  if (experiment == "map_11") {

    if (stripe_width != 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    if (interface != VANILLA) {
      std::cerr << "experiment map/11: only supports vanilla i/o interface" << std::endl;
      return -1;
    }

    if (use_stripe_groups) {
      std::cerr << "cannot use stripe groups with 1:1 workloads" << std::endl;
      return -1;
    }

    workload = new Map11_Workload(&ioctx, entry_size,
        qdepth, op_history, prefix, tp_sec, interface);

  /*
   *
   * =================== map/n1 ======================
   */
  } else if (experiment == "map_n1") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    if (interface != VANILLA &&
        interface != CLS_NO_INDEX &&
        interface != CLS_FULL) {
      std::cerr << "experiment map/n1: doesn't support interface "
        << interface_name << std::endl;
      return -1;
    }

    if (use_stripe_groups && interface == CLS_FULL) {
      std::cerr << "cannot use stripe groups and objects that need init" << std::endl;
      return -1;
    }

    workload = new MapN1_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec, interface, use_stripe_groups);

  /*
   *
   * =================== stream/11 ======================
   */
  } else if (experiment == "bytestream_11") {

    if (stripe_width != 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    if (interface != VANILLA) {
      std::cerr << "experiment stream/11: only supports vanilla i/o interface" << std::endl;
      return -1;
    }

    if (use_stripe_groups) {
      std::cerr << "cannot use stripe groups with 1:1 workloads" << std::endl;
      return -1;
    }

    workload = new ByteStream11_Workload(&ioctx, entry_size,
        qdepth, op_history, prefix, tp_sec, interface);

  /*
   *
   * =================== stream/n1/write ======================
   */
  } else if (experiment == "bytestream_n1_write") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    if (interface != VANILLA &&
        interface != CLS_NO_INDEX &&
        interface != CLS_FULL) {
      std::cerr << "experiment bytestream/n1/write: doesn't support interface "
        << interface_name << std::endl;
      return -1;
    }

    if (use_stripe_groups && interface == CLS_FULL) {
      std::cerr << "cannot use stripe groups and objects that need init" << std::endl;
      return -1;
    }

    workload = new ByteStreamN1Write_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec, interface, use_stripe_groups);

  /*
   * =================== stream/n1/append ======================
   */
  } else if (experiment == "bytestream_n1_append") {

    if (stripe_width <= 0) {
      std::cerr << "(--stripe_width): invalid stripe width " << stripe_width
        << " for experiment " << experiment << std::endl;
      return -1;
    }

    if (interface != VANILLA &&
        interface != CLS_NO_INDEX &&
        interface != CLS_CHECK_EPOCH &&
        interface != CLS_FULL) {
      std::cerr << "experiment stream/n1/append: doesn't support interface "
        << interface_name << std::endl;
      return -1;
    }

    if (use_stripe_groups &&
        (interface == CLS_CHECK_EPOCH || interface == CLS_FULL)) {
      std::cerr << "cannot use stripe groups and objects that need init" << std::endl;
      return -1;
    }

    workload = new ByteStreamN1Append_Workload(&ioctx, stripe_width,
        entry_size, qdepth, op_history, prefix, tp_sec, interface, use_stripe_groups);

  } else {
    std::cerr << "invalid experiment name: " << experiment << std::endl;
    return -1;
  }

  workload->start();
  sleep(runtime);
  workload->stop();

  return 0;
}
