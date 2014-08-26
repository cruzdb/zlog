#include <rados/librados.hpp>
#include "libzlog.h"

#define POOL "zlog-test"
#define HOST "localhost"
#define PORT "5678"

int main(int argc, char **argv)
{
  // connect to rados
  librados::Rados cluster;
  cluster.init(NULL);
  cluster.conf_read_file(NULL);
  cluster.conf_parse_env(NULL);
  int ret = cluster.connect();
  assert(ret == 0);

  // open pool i/o context
  librados::IoCtx ioctx;
  ret = cluster.ioctx_create(POOL, ioctx);
  assert(ret == 0);

  // setup the log
  zlog::SeqrClient client(HOST, PORT);
  client.Connect();

  zlog::Log log;
  ret = zlog::Log::OpenOrCreate(ioctx, "mylog2", 5, &client, log);
  assert(ret == 0);

  // check that tail
  for (;;) {
    uint64_t tail;
    ret = log.CheckTail(&tail, true);
    assert(ret == 0);
  }
}
