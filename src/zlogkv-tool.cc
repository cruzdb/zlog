#include <iostream>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "libzlog/log_impl.h"
#include <map>
#include <libzlog/zlog-kv.h>

namespace po = boost::program_options;
// constructor
// TODO: Add destructor
ZlogKV::ZlogKV(zlog::Log *log)
	: log_(log)
{
}
int main(int argc, char **argv)
{
  std::string pool;
  std::string log_name;
  std::string server;
  std::string port;
  int width;

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
  
  // key and value to be inserted
  
  std::string key = "key";
  ceph::bufferlist bl;
  char data[10] = "data";
  bl.append(data, sizeof(data));
  
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

  zlog::SeqrClient *client = NULL;
  client = new zlog::SeqrClient(server.c_str(), port.c_str());
  client->Connect();

  zlog::Log *log;
  ret = zlog::Log::OpenOrCreate(ioctx, log_name, client, &log);
  
  
  // constructor call
  ZlogKV *zlogkv = NULL;
  zlogkv = new ZlogKV(log);
  
  zlogkv->insert(key, bl);
  zlogkv->read(key);
  
  ioctx.close();
  cluster.shutdown();
  return 0;
}

