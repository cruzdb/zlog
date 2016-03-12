#include <atomic>
#include <condition_variable>
#include <iostream>
#include <fstream>
#include <boost/program_options.hpp>
#include <signal.h>
#include <rados/librados.hpp>
#include "common.h"

namespace po = boost::program_options;

// simulates the sequencer service
static std::atomic_ullong seq;

/*
 * track in-flight ios. the main thread creating and dispatching ios maintains
 * a target qdepth, and when an io completes the outstanding_ios is
 * decremented and the condition variable is notified.
 */
static std::atomic_ullong outstanding_ios;
static std::condition_variable io_cond;
static std::mutex io_lock;

/*
 * track operation latency. when an aio completes its latency is stored in the
 * op_history list which is dumped out after the program exits.
 */
struct op {
  uint64_t start_ns;
  uint64_t latency_ns;
};
static std::vector<op> op_history;
static std::mutex op_history_lock;

// ctrl-c to stop
static volatile int stop = 0;
static void sigint_handler(int sig) {
  stop = 1;
}

static std::string get_oid(unsigned long long seq, size_t stripe_width)
{
  std::stringstream oid;
  size_t stripe_offset = seq % stripe_width;
  oid << "log." << stripe_offset;
  return oid.str();
}

static size_t get_oid_offset(unsigned long long seq, size_t entry_size, size_t stripe_width)
{
  return seq / stripe_width * entry_size;
}

/*
 * aio_write callback
 */
struct aio_state {
  librados::AioCompletion *rc;
  uint64_t submitted_ns;
};

static void handle_io_cb(librados::completion_t cb, void *arg)
{
  aio_state *io = (aio_state*)arg;

  // timing
  uint64_t submitted_ns = io->submitted_ns;
  uint64_t latency_ns = getns() - submitted_ns;

  // clean-up
  outstanding_ios--;
  assert(io->rc->get_return_value() == 0);
  io->rc->release();
  io_cond.notify_one();
  delete io;

  // record
  std::lock_guard<std::mutex> l(op_history_lock);
  op_history.emplace_back(op{submitted_ns, latency_ns});
}

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

  signal(SIGINT, sigint_handler);

  op_history.reserve(2000000);

  // fill with random data
  char data[entry_size];

  std::unique_lock<std::mutex> lock(io_lock);

  for (;;) {
    while (outstanding_ios < qdepth) {
      // create context to track the io
      aio_state *io = new aio_state;
      io->rc = librados::Rados::aio_create_completion(io, NULL, handle_io_cb);
      assert(io->rc);

      // setup io
      std::string oid = get_oid(seq, stripe_width);
      size_t offset = get_oid_offset(seq, entry_size, stripe_width);
      ceph::bufferlist bl;
      bl.append(data, entry_size);

      //  submit the io
      io->submitted_ns = getns();
      ret = ioctx.aio_write(oid, io->rc, bl, bl.length(), offset);
      assert(ret == 0);

      outstanding_ios++;
      seq++;

#if 0
      std::cout << "wrote seq " << seq << " into " << oid
        << " at offset " << offset << " .. "
        << offset+bl.length() << std::endl;
#endif
    }

    io_cond.wait(lock, [&]{ return outstanding_ios < qdepth; });

    if (stop)
      break;
  }

  if (perf_file != "") {
    std::lock_guard<std::mutex> l(op_history_lock);

    std::ofstream ofs;
    if (perf_file != "-")
      ofs.open(perf_file, std::ios::out|std::ios::trunc);

    std::ostream& os = perf_file == "-" ? std::cout : ofs;

    for (auto& e : op_history) {
      os << e.start_ns << " " << e.latency_ns << std::endl;
    }

    os.flush();
    if (ofs.is_open())
      ofs.close();
  }

  return 0;

}
