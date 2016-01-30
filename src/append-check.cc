#include <unistd.h>
#include <map>
#include <mutex>
#include <thread>
#include <iostream>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "libzlog.hpp"

namespace po = boost::program_options;

static volatile int stop = 0;
static void sigint_handler(int sig) {
  std::cout << "stopping" << std::endl;
  stop = 1;
}

static std::mutex lock;
static std::map<uint64_t, int> appends;

static void check_appends(std::string pool, std::string server,
    std::string port, std::string log_name)
{
  // connect
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  cluster.conf_parse_env(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  zlog::SeqrClient *client;
  client = new zlog::SeqrClient(server.c_str(), port.c_str());
  client->Connect();

  zlog::LogHL *log;
  ret = zlog::LogHL::OpenOrCreate(ioctx, log_name, client, &log);
  assert(ret == 0);

  int count = 0;
  while (!stop) {
    lock.lock();
    if (appends.empty()) {
      lock.unlock();
      sleep(1);
      continue;
    }
    auto it = appends.begin();
    std::advance(it, rand() % appends.size());
    uint64_t pos = it->first;
    int value = it->second;
    lock.unlock();

    ceph::bufferlist bl;
    int ret = log->Read(pos, bl);
    assert(ret == 0);

    assert(memcmp(bl.c_str(), (char*)&value, sizeof(value)) == 0);

    if (++count % 1000 == 0)
      std::cout << "Check pos " << pos << std::endl;
  }

  ioctx.close();
  cluster.shutdown();
}

int main(int argc, char **argv)
{
  std::string pool;
  std::string log_name;
  std::string server;
  std::string port;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("pool", po::value<std::string>(&pool)->required(), "Pool name")
    ("logname", po::value<std::string>(&log_name)->required(), "Log name")
    ("server", po::value<std::string>(&server)->required(), "Server host")
    ("port", po::value<std::string>(&port)->required(), "Server port")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  // connect
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  cluster.conf_parse_env(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(pool.c_str(), ioctx);
  assert(ret == 0);

  signal(SIGINT, sigint_handler);

  zlog::SeqrClient *client;
  client = new zlog::SeqrClient(server.c_str(), port.c_str());
  client->Connect();

  zlog::LogHL *log;
  ret = zlog::LogHL::OpenOrCreate(ioctx, log_name, client, &log);
  assert(ret == 0);

  std::thread check_thread(check_appends, pool, server, port, log_name);

  while (!stop) {
    int value = rand();
    char bytes[sizeof(value)];
    memcpy(bytes, &value, sizeof(value));

    ceph::bufferlist bl;
    bl.append(bytes, sizeof(bytes));

    uint64_t pos;
    int ret = log->Append(bl, &pos);
    assert(ret == 0);

    std::cout << "Append: " << pos << std::endl;

    //usleep(300000);

    lock.lock();
    appends[pos] = value;
    lock.unlock();
  }

  check_thread.join();

  delete log;
  ioctx.close();
  cluster.shutdown();

  return 0;
}
