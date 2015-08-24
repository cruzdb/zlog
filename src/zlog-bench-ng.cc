#include <sstream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <boost/program_options.hpp>
#include <condition_variable>
#include <rados/librados.hpp>
#include "libzlog.h"

namespace po = boost::program_options;

struct AioState {
  zlog::Log::AioCompletion *c;
  uint64_t position;
};

static std::condition_variable io_cond;
static std::mutex io_lock;
std::atomic<uint64_t> outstanding_ios;

static void safe_cb(librados::completion_t cb, void *arg)
{
  AioState *s = (AioState*)arg;
  assert(s->c->get_return_value() == 0);
  std::cout << s->position << std::endl;
  outstanding_ios--;
  s->c->release();
  delete s;
  io_cond.notify_one();
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
      uint64_t tail = seq_.fetch_add(1); // returns previous value
      *position = tail + 1;
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

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&logname_req)->default_value(""), "Log name")
    ("width", po::value<int>(&width)->required(), "Width")
    ("qdepth", po::value<int>(&qdepth)->default_value(1), "Queue depth")
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

  // build a log name
  std::stringstream logname;
  if (logname_req.size())
    logname << logname_req;
  else {
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    logname << uuid;
  }
  logname << ".log";

  // setup log instance
  zlog::Log log;
  FakeSeqrClient client(logname.str());
  ret = zlog::Log::OpenOrCreate(ioctx, logname.str(), width, &client, log);
  client.Init(ioctx);
  assert(ret == 0);

  // this is just a little hack that forces the epoch to be refreshed in the
  // log instance. otherwise when we blast out a bunch of async requests they
  // all end up having old epochs.
  ceph::bufferlist bl;
  log.Append(bl);

  std::unique_lock<std::mutex> lock(io_lock);

  outstanding_ios = 0;
  for (;;) {
    while (outstanding_ios < qdepth) {
      AioState *state = new AioState;
      state->c = zlog::Log::aio_create_completion(state, safe_cb);
      assert(state->c);
      ret = log.AioAppend(state->c, bl, &state->position);
      assert(ret == 0);
      outstanding_ios++;
    }
    io_cond.wait(lock, [&]{ return outstanding_ios < qdepth; });
  }

  return 0;
}
