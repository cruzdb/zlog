//#include <cerrno>
#include <iostream>
#include <cstdlib>
//#include <sstream>
#include <string>
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "libzlog.hpp"
//#include "zlog.pb.h"
//#include "protobuf_bufferlist_adapter.h"
//#include "internal.hpp"
using namespace std;

int64_t find_pool(const std::string &pool_name, librados::Rados &cluster)
{
  char *id = getenv("CEPH_CLIENT_ID");
  if (id) std::cerr << "Client id is: " << id << std::endl;

  int ret;
  ret = cluster.init(id);
  if (ret) {
    std::cerr << "cluster.init failed with error " << ret << std::endl;
    return -ENOENT;
  }
  ret = cluster.conf_read_file(NULL);
  if (ret) {
    cluster.shutdown();
    std::cerr << "cluster.conf_read_file failed with error " << ret
              << std::endl;
    return -ENOENT;
  }
  cluster.conf_parse_env(NULL);
  ret = cluster.connect();
  if (ret) {
    cluster.shutdown();
    std::cerr << "cluster.connect failed with error " << ret << std::endl;
    return -ENOENT;
  }
  ret = cluster.pool_lookup(pool_name.c_str());
  if (ret == -ENOENT) {
    cluster.shutdown();
    std::cerr << "cluster.pool_lookup(" << pool_name << ") failed with error "
              << ret << std::endl;
  }
  return ret;
}

int main(int argc, char *argv[])
{
  int log_stripe_size;
  int64_t ret;
  if(argc!=4)
  {
    cout << "Arguments required log, pool, stripe size\n";
    exit(1);
  }
  string log_name(argv[1]);
  string log_pool(argv[2]);
  log_stripe_size = atoi(argv[3]);

  if (log_stripe_size < 1)
  {
    cout << "Invalid stripe size provided: " << argv[3] << "\n";
    exit(1);
  }
  
  librados::IoCtx ioctx;
  librados::Rados rados;
  ret = find_pool(log_pool, rados);
  if (ret == -ENOENT) {
    cerr << "Pool not found : " << log_pool << endl;
    exit(1);
  }
 
  ret = rados.ioctx_create(log_pool.c_str(), ioctx);
  assert(ret == 0);
  zlog::Log log;
  ret = zlog::Log::Open(ioctx, log_name, NULL, log);
  assert(ret == 0);

  ret = log.UpdateLayout(ioctx, log_stripe_size);
  assert(ret == 0);
  return 0;

}
 
