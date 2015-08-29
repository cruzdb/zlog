#include <sstream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <boost/program_options.hpp>
#include <condition_variable>
#include <signal.h>
#include <chrono>
#include <atomic>
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
static std::atomic<uint64_t> latency_ms;

static volatile int stop = 0;
static void sigint_handler(int sig) {
  stop = 1;
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

  auto diff_ms = std::chrono::duration_cast<
    std::chrono::milliseconds>(completed - s->submitted);
  latency_ms += diff_ms.count();

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

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&logname_req)->default_value(""), "Log name")
    ("width", po::value<int>(&width)->required(), "Width")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
    ("iosize", po::value<int>(&iosize)->default_value(0), "IO Size")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  assert(qdepth > 0);

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

  std::unique_lock<std::mutex> lock(io_lock);

  ios_completed = 0;
  ios_completed_total = 0;
  outstanding_ios = 0;
  latency_ms = 0;

  char iobuf[iosize];

  auto start = std::chrono::steady_clock::now();
  for (;;) {
    uint64_t ios_completed_end = ios_completed;
    uint64_t latency_ms_end = latency_ms;
    auto end = std::chrono::steady_clock::now();
    std::chrono::duration<double> diff = std::chrono::duration_cast<
      std::chrono::duration<double>>(end - start);
    double secs = diff.count();
    if (secs > 5) {
      double ios_per_sec = (double)ios_completed_end / secs;
      double avg_ms_lat = (double)latency_ms_end / (double)ios_completed_end;
      std::cout << "total_iops: " << ios_completed_total <<
        " iops: " << ios_per_sec <<
        " avg_lat_ms: " << avg_ms_lat << std::endl;
      ios_completed = 0;
      latency_ms = 0;
      start = std::chrono::steady_clock::now();
    }

    while (outstanding_ios < qdepth) {

      AioState *state = new AioState;

      for (unsigned i = 0; i < iosize; i++) {
        iobuf[i] = (char)rand();
      }

      state->append_bl.append(iobuf, iosize);
      state->log = &log;

      state->c = zlog::Log::aio_create_completion(state, handle_append_cb);
      assert(state->c);
      state->submitted = std::chrono::steady_clock::now();
      ret = log.AioAppend(state->c, state->append_bl, &state->position);
      assert(ret == 0);
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

  return 0;
}
