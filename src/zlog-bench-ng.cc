#include <sstream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <boost/program_options.hpp>
#include <condition_variable>
#include <signal.h>
#include <chrono>
#include <atomic>
#include <thread>
#include <random>
#include <rados/librados.hpp>
#include "libzlog.h"

namespace po = boost::program_options;

//#define VERIFY_IOS
//#define SLOPPY_SEQ

struct AioState {
  zlog::Log *log;
  ceph::bufferlist append_bl;
  ceph::bufferlist read_bl;
  zlog::Log::AioCompletion *c;
  uint64_t position;
  std::chrono::time_point<std::chrono::steady_clock> submitted;
};

static std::condition_variable io_cond;
static std::mutex io_lock;
static std::atomic<uint64_t> outstanding_ios;
static std::atomic<uint64_t> ios_completed;
static std::atomic<uint64_t> ios_completed_total;
static std::atomic<uint64_t> latency_us;

static volatile int stop = 0;
static void sigint_handler(int sig) {
  stop = 1;
}

static void report()
{
  while (!stop) {
    auto start = std::chrono::steady_clock::now();
    uint64_t ios_completed_start = ios_completed;
    uint64_t latency_us_start = latency_us;

    sleep(5);
    if (stop)
      break;

    auto end = std::chrono::steady_clock::now();
    uint64_t ios_completed_end = ios_completed;
    uint64_t latency_us_end = latency_us;

    auto diff = std::chrono::duration_cast<
        std::chrono::duration<double>>(end - start);

    double ios_per_sec = (double)(ios_completed_end - ios_completed_start) / diff.count();
    double avg_us_lat = (double)(latency_us_end - latency_us_start) /
      (double)(ios_completed_end - ios_completed_start);
    double avg_ms_lat = avg_us_lat / (double)1000.0;

    std::cout << "period: " << diff.count() <<
      " total_iops: " << ios_completed_total <<
      " iops: " << ios_per_sec <<
      " avg_lat_ms: " << avg_ms_lat << std::endl;
  }
}

#ifdef VERIFY_IOS
static void verify_append_cb(zlog::Log::AioCompletion::completion_t cb,
    void *arg)
{
  AioState *s = (AioState*)arg;

  assert(s->c->get_return_value() == 0);
  s->c->release();

  assert(s->read_bl == s->append_bl);
  int sum1 = 0, sum2 = 0;
  for (unsigned i = 0; i < s->read_bl.length(); i++) {
    sum1 += (int)s->read_bl[i];
    sum2 += (int)s->append_bl[i];
  }
  assert(sum1 == sum2);

  delete s;
}
#endif

static void handle_append_cb(zlog::Log::AioCompletion::completion_t cb,
    void *arg)
{
  AioState *s = (AioState*)arg;
  auto completed = std::chrono::steady_clock::now();
  zlog::Log *log = s->log;

  ios_completed++;
  ios_completed_total++;
  outstanding_ios--;
  io_cond.notify_one();

  assert(s->c->get_return_value() == 0);
  s->c->release();
  s->c = NULL;

  auto diff_us = std::chrono::duration_cast<
    std::chrono::microseconds>(completed - s->submitted);
  latency_us += diff_us.count();

#ifdef VERIFY_IOS
  if (s->append_bl.length() > 0)
    assert(!(s->append_bl == s->read_bl));
  s->c = zlog::Log::aio_create_completion(s, verify_append_cb);
  int ret = log->AioRead(s->position, s->c, &s->read_bl);
  assert(ret == 0);
#else
  delete s;
#endif
}

static void handle_read_cb(zlog::Log::AioCompletion::completion_t cb,
    void *arg)
{
  AioState *s = (AioState*)arg;
  auto completed = std::chrono::steady_clock::now();

  ios_completed++;
  ios_completed_total++;
  outstanding_ios--;
  io_cond.notify_one();

  int op_rv = s->c->get_return_value();
  if (op_rv) {
    std::cout << op_rv << " " << s->position << std::endl;
  }
  assert(s->c->get_return_value() == 0);
  assert(s->read_bl.length() > 0);

  s->c->release();
  s->c = NULL;

  auto diff_us = std::chrono::duration_cast<
    std::chrono::microseconds>(completed - s->submitted);
  latency_us += diff_us.count();

  delete s;
}

static void workload(zlog::Log *log, bool read_mode, uint64_t tail, size_t iosize)
{
  std::random_device rd;
  std::mt19937 gen(rd());
  std::uniform_int_distribution<unsigned long long> dis(50, tail);
  if (read_mode)
    std::cout << "tail generation: " << dis.min() << " .. " << dis.max() << std::endl;

  char iobuf[iosize];

  while (!stop) {
    auto start = std::chrono::steady_clock::now();
    if (read_mode) {
      uint64_t pos = dis(gen);
      ceph::bufferlist bl;
      int ret = log->Read(pos, bl);
      assert(ret == 0);
      assert(bl.length() > 0);
    } else {
      for (unsigned i = 0; i < iosize; i++) {
        iobuf[i] = (char)rand();
      }
      uint64_t pos = 0;
      ceph::bufferlist bl;
      bl.append(iobuf, iosize);
      int ret = log->Append(bl, &pos);
      assert(ret == 0);
      assert(pos > 0);
    }
    auto end = std::chrono::steady_clock::now();
    auto diff_us = std::chrono::duration_cast<
      std::chrono::microseconds>(end - start);
    latency_us += diff_us.count();
    //std::cout << diff_us.count() << std::endl;
    ios_completed++;
    ios_completed_total++;
  }
}

class FakeSeqrClient : public zlog::SeqrClient {
 public:
  FakeSeqrClient(const std::string& name) :
    SeqrClient("", ""), seq_(0), name_(name)
  {
    assert(seq_.is_lock_free());
  }

  void Init(librados::IoCtx& ioctx) {
    zlog::Log log;
    int ret = zlog::Log::Open(ioctx, name_, NULL, log);
    assert(ret == 0);

    uint64_t epoch;
    ret = log.SetProjection(&epoch);
    assert(ret == 0);

    ret = log.Seal(epoch);
    assert(ret == 0);

    uint64_t position;
    ret = log.FindMaxPosition(epoch, &position);
    assert(ret == 0);

    epoch_ = epoch;
    seq_.store(position);

    std::cout << "init seq: pos=" << seq_.load() << std::endl;
  }

  void Connect() {}

  int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, uint64_t *position, bool next)
  {
    assert(name == name_);

    if (epoch_ < epoch)
      return -ERANGE;

    if (next) {
#ifdef SLOPPY_SEQ
      if (seq_ > 100 && seq_ % 10 == 0) {
        *position = seq_ / 2;
        seq_++;
      } else {
        uint64_t tail = seq_.fetch_add(1); // returns previous value
        *position = tail + 1;
      }
#else
      uint64_t tail = seq_.fetch_add(1); // returns previous value
      *position = tail + 1;
#endif
    } else
      *position = seq_.load();

    return 0;
  }

 private:
  std::atomic<uint64_t> seq_;
  std::string name_;
  uint64_t epoch_;
};

int main(int argc, char **argv)
{
  int width;
  std::string pool;
  std::string logname_req;
  int qdepth;
  int iosize;
  bool read_mode;
  bool threaded;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&logname_req)->default_value(""), "Log name")
    ("width", po::value<int>(&width)->required(), "Width")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
    ("iosize", po::value<int>(&iosize)->default_value(0), "IO Size")
    ("read", po::value<bool>(&read_mode)->default_value(false), "Read mode")
    ("threaded", po::value<bool>(&threaded)->default_value(false), "Threaded mode")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  assert(qdepth > 0);

  if (read_mode)
    assert(logname_req.length());

  // connect to rados
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  cluster.conf_parse_env(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool i/o context
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  signal(SIGINT, sigint_handler);

  // build a log name
  std::string logname;
  {
    std::stringstream ss;
    if (logname_req.size())
      ss << logname_req;
    else {
      boost::uuids::uuid uuid = boost::uuids::random_generator()();
      ss << uuid;
    }
    ss << ".log";
    logname = ss.str();
  }

  // setup log instance
  zlog::Log log;
  FakeSeqrClient client(logname);
  ret = zlog::Log::OpenOrCreate(ioctx, logname, width, &client, log);
  client.Init(ioctx);
  assert(ret == 0);

  // this is just a little hack that forces the epoch to be refreshed in the
  // log instance. otherwise when we blast out a bunch of async requests they
  // all end up having old epochs.
  ceph::bufferlist bl;
  log.Append(bl);

  /*
   * For read mode we look up the current tail and then issue random reads
   * within the range of the log.
   */
  uint64_t tail = 0;
  if (read_mode) {
    ret = log.CheckTail(&tail, false);
    assert(!ret);
    // teardown/setup is sloppy, so we trim off a bit so we don't hit any
    // unwritten entries.
    std::cout << "read mode tail: " << tail << std::endl;
    tail -= 50;
    assert(tail > 0);
  }

  std::unique_lock<std::mutex> lock(io_lock);

  ios_completed = 0;
  ios_completed_total = 0;
  outstanding_ios = 0;
  latency_us = 0;

  std::thread reporting_thread(report);
  std::vector<std::thread> workload_threads;

  if (threaded) {
    std::cout << "threaded mode" << std::endl;
    for (unsigned i = 0; i < qdepth; i++) {
      std::thread t(workload, &log, read_mode, tail, iosize);
      workload_threads.push_back(std::move(t));
    }
  } else {
    std::random_device rd;
    std::mt19937 gen(rd());
    // skip the front of the log if there was some problems getting this setup
    // and those entries were skipped or filled.
    std::uniform_int_distribution<unsigned long long> dis(50, tail);
    if (read_mode)
      std::cout << "tail generation: " << dis.min() << " .. " << dis.max() << std::endl;

    char iobuf[iosize];

    for (;;) {
      while (outstanding_ios < qdepth) {

        AioState *state = new AioState;

        state->log = &log;

        if (read_mode) {
          state->position = dis(gen);
          state->c = zlog::Log::aio_create_completion(state, handle_read_cb);
          assert(state->c);
          state->submitted = std::chrono::steady_clock::now();
          ret = log.AioRead(state->position, state->c, &state->read_bl);
          assert(ret == 0);
        } else {
          state->c = zlog::Log::aio_create_completion(state, handle_append_cb);
          assert(state->c);
          for (unsigned i = 0; i < iosize; i++) {
            iobuf[i] = (char)rand();
          }
          state->append_bl.append(iobuf, iosize);
          state->submitted = std::chrono::steady_clock::now();
          ret = log.AioAppend(state->c, state->append_bl, &state->position);
          assert(ret == 0);
        }

        outstanding_ios++;
      }
      io_cond.wait(lock, [&]{ return outstanding_ios < qdepth; });

      if (stop)
        break;
    }

    // draining the ios is useful for running the read workload because
    // otherwise there is a section near the tail of the log that has unwritten
    // entries that would otherwise need to be handled in some way when they
    // were read.
    while (1) {
      std::cout << "draining ios: " << outstanding_ios << " remaining" << std::endl;
      if (outstanding_ios == 0)
        break;
      sleep(1);
    }
  }


  for (auto it = workload_threads.begin();
       it != workload_threads.end(); it++) {
    it->join();
  }

  reporting_thread.join();

  return 0;
}
