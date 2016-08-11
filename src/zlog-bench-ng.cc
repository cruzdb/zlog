#include <signal.h>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <thread>
#include <boost/program_options.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "libzlog/log_impl.h"
#include "include/zlog/ceph_backend.h"

namespace po = boost::program_options;

//#define VERIFY_IOS
//#define SLOPPY_SEQ

struct AioState {
  zlog::LogImpl *log;
  ceph::bufferlist append_bl;
  std::string read_str;
  zlog::AioCompletion *c;
  librados::AioCompletion *rc; // used by append workload
  uint64_t position;
  std::chrono::time_point<std::chrono::steady_clock> submitted;
};

static std::condition_variable io_cond;
static std::mutex io_lock;
static std::atomic<uint64_t> outstanding_ios;
static std::atomic<uint64_t> ios_completed;
static std::atomic<uint64_t> ios_completed_total;
static std::atomic<uint64_t> latency_us;

static uint64_t start_realtime_ns;
static uint64_t start_monotonic_ns;
static std::vector<std::pair<uint64_t, uint64_t>> latencies;

static volatile int stop = 0;
static void sigint_handler(int sig) {
  stop = 1;
}

static uint64_t run_start_ns;
static uint64_t run_end_ns;

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  int ret = clock_gettime(clock, &ts);
  assert(ret == 0);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getns()
{
  return __getns(CLOCK_MONOTONIC);
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
static void verify_append_cb(AioState *s)
{
  assert(s->c->ReturnValue() == 0);
  delete s->c;

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

static void handle_append_cb(AioState *s)
{
  auto completed = std::chrono::steady_clock::now();
  zlog::LogImpl *log = s->log;

  ios_completed++;
  ios_completed_total++;
  outstanding_ios--;
  io_cond.notify_one();

  assert(s->c->ReturnValue() == 0);
  delete s->c;
  s->c = NULL;

  auto diff_us = std::chrono::duration_cast<
    std::chrono::microseconds>(completed - s->submitted);
  latency_us += diff_us.count();

#ifdef VERIFY_IOS
  if (s->append_bl.length() > 0)
    assert(!(s->append_bl == s->read_bl));
  s->c = zlog::Log::aio_create_completion(std::bind(verify_append_cb, s));
  int ret = log->AioRead(s->position, s->c, &s->read_bl);
  assert(ret == 0);
#else
  delete s;
#endif
}

static void handle_bulk_append_cb(librados::completion_t cb, void *arg)
{
  AioState *s = (AioState*)arg;
  auto completed = std::chrono::steady_clock::now();

  ios_completed++;
  ios_completed_total++;
  outstanding_ios--;
  io_cond.notify_one();

  assert(s->rc->get_return_value() == 0);
  s->rc->release();
  s->rc = NULL;

  auto diff_us = std::chrono::duration_cast<
    std::chrono::microseconds>(completed - s->submitted);
  latency_us += diff_us.count();

#ifdef VERIFY_IOS
  assert(0);
#else
  delete s;
#endif
}

static void handle_read_cb(AioState *s)
{
  auto completed = std::chrono::steady_clock::now();

  ios_completed++;
  ios_completed_total++;
  outstanding_ios--;
  io_cond.notify_one();

  int op_rv = s->c->ReturnValue();
  if (op_rv) {
    std::cout << op_rv << " " << s->position << std::endl;
  }
  assert(s->c->ReturnValue() == 0);
  assert(s->read_str.size() > 0);

  delete s->c;
  s->c = NULL;

  auto diff_us = std::chrono::duration_cast<
    std::chrono::microseconds>(completed - s->submitted);
  latency_us += diff_us.count();

  delete s;
}

class FakeSeqrClient : public zlog::SeqrClient {
 public:
  FakeSeqrClient(const std::string& name) :
    SeqrClient("", ""), seq_(0), name_(name)
  {
    assert(seq_.is_lock_free());
  }

  void Init(librados::IoCtx& ioctx) {
    zlog::Log *baselog;
    CephBackend *be = new CephBackend(&ioctx);
    int ret = zlog::LogImpl::Open(be, name_, NULL, &baselog);
    assert(ret == 0);
    zlog::LogImpl *log = reinterpret_cast<zlog::LogImpl*>(baselog);

    uint64_t epoch;
    uint64_t position;
    ret = log->CreateCut(&epoch, &position);
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
        *position = tail;
      }
#else
      uint64_t tail = seq_.fetch_add(1); // returns previous value
      *position = tail;
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

static void do_cdf(std::string filename)
{
  // sort latencies by latency value
  const size_t num_latencies = latencies.size();
  std::sort(latencies.begin(), latencies.end(),
      [](const std::pair<uint64_t, uint64_t>& a,
        const std::pair<uint64_t, uint64_t>& b) {
      return a.second < b.second;
      });

  // compute cdf
  std::vector<double> ecdf;
  ecdf.reserve(num_latencies);
  for (size_t count = 0; count < num_latencies; count++) {
    double p = (double)count / (double)num_latencies;
    ecdf.push_back(p);
  }

  // the cdf might have duplicate latencies. we'll take the min of those
  // ranges, and also include the largest value.
  std::map<uint64_t, size_t> pts;
  for (size_t i = 0; i < num_latencies; i++) {
    auto lat = latencies[i].second;
    auto it = pts.find(lat);
    if (it == pts.end())
      pts[lat] = i;
  }

  // fixup end point
  uint64_t max_lat = latencies[num_latencies-1].second;
  assert(pts.find(max_lat) != pts.end());
  pts[max_lat] = num_latencies - 1;

  // iops
  uint64_t ios = num_latencies;
  uint64_t dur_ns = run_end_ns - run_start_ns;
  double iops = (double)(ios * 1000000000ULL) / (double)dur_ns;

  int fd = 0;
  fd = open(filename.c_str(), O_WRONLY|O_CREAT|O_TRUNC, 0644);
  assert(fd > 0);

  // average throughput
  dprintf(fd, "%f\n", iops);

  // latency cdf
  for (auto it = pts.begin(); it != pts.end(); it++) {
    auto lat = latencies[it->second].second;
    auto pct = ecdf[it->second];
    dprintf(fd, "%llu,%f\n", (unsigned long long)lat, pct);
  }

  fsync(fd);
  close(fd);
}

int main(int argc, char **argv)
{
  int width;
  std::string pool;
  std::string logname_req;
  int qdepth;
  int iosize;
  bool read_mode;
  bool sync;
  std::string server;
  std::string port;
  bool track_latency;
  std::string outfile;
  bool testseqr;
  bool append;
  bool cdf;
  int runtime;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&logname_req)->default_value(""), "Log name")
    ("width", po::value<int>(&width)->default_value(0), "Width")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
    ("iosize", po::value<int>(&iosize)->default_value(0), "IO Size")
    ("read", po::value<bool>(&read_mode)->default_value(false), "Read mode")
    ("sync", po::value<bool>(&sync)->default_value(false), "Sync mode")
    ("server", po::value<std::string>(&server)->default_value(""), "Server host")
    ("port", po::value<std::string>(&port)->default_value("-1"), "Server port")
    ("latency", po::value<bool>(&track_latency)->default_value(false), "Track latencies")
    ("outfile", po::value<std::string>(&outfile)->default_value(""), "Output file")
    ("runtime", po::value<int>(&runtime)->default_value(0), "runtime")
    ("testseqr", po::value<bool>(&testseqr)->default_value(false), "Measure seqr throughput")
    ("append", po::value<bool>(&append)->default_value(false), "Append benchmark")
    ("cdf", po::value<bool>(&cdf)->default_value(false), "dump cdf")
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

  // the append workload creates @width number of objects and then does a blob
  // append to the objects.
  std::vector<std::string> append_oids;
  if (append) {
      assert(width > 0);
      for (size_t i = 0; i < width; i++) {
          std::stringstream oid;
          oid << logname << "." << i;
          append_oids.push_back(oid.str());
      }
  }

  // setup log instance
  zlog::SeqrClient *client;
  if (server.length()) {
    client = new zlog::SeqrClient(server.c_str(), port.c_str());
    client->Connect();
  } else {
    client = new FakeSeqrClient(logname);
  }
  zlog::Log *baselog;
  CephBackend *be = new CephBackend(&ioctx);
  ret = zlog::LogImpl::OpenOrCreate(be, logname, client, &baselog);
  assert(ret == 0);
  zlog::LogImpl *log = reinterpret_cast<zlog::LogImpl*>(baselog);

  if (server.length() == 0) {
    FakeSeqrClient *c = static_cast<FakeSeqrClient*>(client);
    c->Init(ioctx);
  }

  // this is just a little hack that forces the epoch to be refreshed in the
  // log instance. otherwise when we blast out a bunch of async requests they
  // all end up having old epochs.
  log->Append(Slice());

  /*
   * For read mode we look up the current tail and then issue random reads
   * within the range of the log.
   */
  uint64_t tail = 0;
  if (read_mode) {
    ret = log->CheckTail(&tail, false);
    assert(!ret);
    // teardown/setup is sloppy, so we trim off a bit so we don't hit any
    // unwritten entries.
    std::cout << "read mode tail: " << tail << std::endl;
    tail -= 50;
    assert(tail > 0);
  }
  std::random_device rd;
  std::mt19937 gen(rd());
  // skip the front of the log if there was some problems getting this setup
  // and those entries were skipped or filled.
  std::uniform_int_distribution<unsigned long long> dis(50, tail);
  if (read_mode)
    std::cout << "tail generation: " << dis.min() << " .. " << dis.max() << std::endl;

  std::unique_lock<std::mutex> lock(io_lock);

  ios_completed = 0;
  ios_completed_total = 0;
  outstanding_ios = 0;
  latency_us = 0;

  if (track_latency)
    latencies.reserve(20000000);

  char iobuf[iosize];

  std::thread reporting_thread(report);

  std::thread stopper{[&] {
    if (runtime) {
      sleep(runtime);
      stop = 1;
    }
  }};

  start_monotonic_ns = getns();
  start_realtime_ns = __getns(CLOCK_REALTIME);

  if (testseqr) {
    std::cout << "seqr throughput mode" << std::endl;
    for (int i = 0; i < 10; i++) {
      uint64_t pos;
      int ret = log->CheckTail(&pos, true);
      assert(ret == 0);
    }
    run_start_ns = getns();
    while (!stop) {
      uint64_t pos;
      uint64_t start_ns = getns();
      int ret = log->CheckTail(&pos, true);
      uint64_t latency_ns = getns() - start_ns;
      assert(ret == 0);
      if (track_latency)
        latencies.push_back(std::make_pair(start_ns, latency_ns));
      latency_us += (latency_ns / 1000);
      ios_completed++;
      ios_completed_total++;
    }
    run_end_ns = getns();
  } else if (sync) {
    std::cout << "sync mode: ignoring qdepth (qdepth=1)" << std::endl;

    while (!stop) {
      uint64_t start_ns, latency_ns;
      if (read_mode) {
        uint64_t pos = dis(gen);
        std::string entry;
        start_ns = getns();
        int ret = log->Read(pos, &entry);
        latency_ns = getns() - start_ns;
        assert(ret == 0);
        assert(entry.size() > 0);
      } else {
        for (unsigned i = 0; i < iosize; i++) {
          iobuf[i] = (char)rand();
        }
        uint64_t pos = 0;
        start_ns = getns();
        int ret = log->Append(Slice(iobuf, iosize), &pos);
        latency_ns = getns() - start_ns;
        assert(ret == 0);
        assert(pos > 0);
      }
      if (track_latency)
        latencies.push_back(std::make_pair(start_ns, latency_ns));
      latency_us += (latency_ns / 1000);
      ios_completed++;
      ios_completed_total++;
    }

  } else {
    size_t append_oid_cnt = append_oids.size();
    size_t append_count = 0; // used to stripe ios in append mode
    for (;;) {
      while (outstanding_ios < qdepth) {
        AioState *state = new AioState;
        state->log = log;
        if (read_mode) {
          state->position = dis(gen);
          state->c = zlog::Log::aio_create_completion(std::bind(handle_read_cb, state));
          assert(state->c);
          state->submitted = std::chrono::steady_clock::now();
          ret = log->AioRead(state->position, state->c, &state->read_str);
          assert(ret == 0);
        } else if (append) {
          // this is a simulation where we grab a sequence number and do an
          // object append to simulate a mapping onto object data rather than
          // omap.
          uint64_t pos;
          ret = log->CheckTail(&pos, true);
          assert(ret == 0);

          //
          state->rc = librados::Rados::aio_create_completion(state, NULL, handle_bulk_append_cb);
          assert(state->rc);
          for (unsigned i = 0; i < iosize; i++) {
            iobuf[i] = (char)rand();
          }
          state->append_bl.append(iobuf, iosize);
          state->submitted = std::chrono::steady_clock::now();

          //
          ret = ioctx.aio_append(append_oids[append_count % append_oid_cnt],
                  state->rc, state->append_bl, (size_t)iosize);
          assert(ret == 0);

          append_count++;
        } else {
          state->c = zlog::Log::aio_create_completion(std::bind(handle_append_cb, state));
          assert(state->c);
          for (unsigned i = 0; i < iosize; i++) {
            iobuf[i] = (char)rand();
          }
          state->append_bl.append(iobuf, iosize);
          state->submitted = std::chrono::steady_clock::now();
          ret = log->AioAppend(state->c, Slice(state->append_bl.c_str(), state->append_bl.length()), &state->position);
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

  stopper.join();
  reporting_thread.join();

  if (cdf) {
    assert(track_latency);
    assert(outfile.size());
    do_cdf(outfile);
  } else if (track_latency) {
    if (outfile.length()) {
      char hostname[1024];
      int ret = gethostname(hostname, sizeof(hostname));
      assert(ret == 0);
      std::stringstream ss;
      ss << outfile << "." << hostname << "." << getpid() << ".txt";
      std::ofstream out;
      out.open(ss.str(), std::ios::trunc);
      out << "init: " << start_realtime_ns << " " << start_monotonic_ns << std::endl;
      for (auto it = latencies.begin(); it != latencies.end(); it++) {
        out << it->first << " " << it->second << std::endl;
      }
      out.close();
    } else {
      std::cout << "init: " << start_realtime_ns << " " << start_monotonic_ns << std::endl;
      for (auto it = latencies.begin(); it != latencies.end(); it++) {
        std::cout << it->first << " " << it->second << std::endl;
      }
    }
  }

  return 0;
}
