#include <iostream>
#include <boost/program_options.hpp>
#include <rados/librados.hpp>
#include "libzlog/log_impl.h"
#include <map>
#include "zlog-kv.h"

namespace po = boost::program_options;
// constructor
// TODO: Add destructor
ZlogKV::ZlogKV(zlog::Log *log)
	: log_(log)
{
}
  
void ZlogKV::insert(std::string& key, ceph::bufferlist& data)
{
  // concat key and data before appending in the log
  ceph::bufferlist zlog_data;
  zlog_data.append(key);
  zlog_data.append(data);

  uint64_t pos;
  // append zlog_data to the log
  int ret = log_->Append(zlog_data, &pos);
  // add key, pos to the kv map
  key_to_position_.insert(std::pair<std::string&, uint64_t>(key, pos));
  std::cout << "Append at position: " << pos << std::endl;
}

void ZlogKV::read(std::string key)
{
  //lookup the map to find the log position
  std::map<std::string, uint64_t>::const_iterator it = 
                                         key_to_position_.find(key); 
  uint64_t pos;
  pos = it->second;
  ceph::bufferlist zlog_data;
  
  // read the data from the log position
  int ret = log_->Read(pos, zlog_data);
  std::cout<<"Read: "<< zlog_data.c_str() << " at position " <<pos << std::endl;
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

