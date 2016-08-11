#include <sstream>
#include <thread>
#include <boost/program_options.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "libzlog/log_impl.h"

namespace po = boost::program_options;

void client_thread(zlog::LogImpl *log, bool check_tail)
{
  // buffer with random bytes
  char buf[4096];
  int fd = open("/dev/urandom", O_RDONLY);
  assert(fd > 0);
  int ret = read(fd, buf, sizeof(buf));
  assert(ret == (int)sizeof(buf));
  close(fd);

  for (;;) {
    uint64_t pos;
    if (check_tail) {
      ret = log->CheckTail(&pos, true);
    } else {
      ret = log->Append(Slice(buf, sizeof(buf)), &pos);
    }
    assert(ret == 0);
  }
}

int main(int argc, char **argv)
{
  int num_threads;
  std::string server;
  std::string pool;
  std::string port;
  std::string logname_req;
  bool check_tail;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("server", po::value<std::string>(&server)->required(), "Server host")
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("port", po::value<std::string>(&port)->required(), "Server port")
    ("threads", po::value<int>(&num_threads)->required(), "Number of threads")
    ("logname", po::value<std::string>(&logname_req)->default_value(""), "Log name")
    ("checktail", po::value<bool>(&check_tail)->default_value(false), "Only check tail")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

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

  std::stringstream logname;
  if (logname_req.size())
    logname << logname_req;
  else {
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    logname << uuid;
  }
  logname << ".log";

  std::vector<std::thread> threads;

  for (int i = 0; i < num_threads; i++) {
    zlog::SeqrClient *client = new zlog::SeqrClient(server.c_str(), port.c_str());
    client->Connect();
    zlog::Log *baselog;
    ret = zlog::LogImpl::OpenOrCreate(ioctx, logname.str(), client, &baselog);
    zlog::LogImpl *log = reinterpret_cast<zlog::LogImpl*>(baselog);
    assert(ret == 0);
    std::thread t(client_thread, log, check_tail);
    threads.push_back(std::move(t));
  }

  for (auto it = threads.begin(); it != threads.end(); it++)
    it->join();

  return 0;
}
