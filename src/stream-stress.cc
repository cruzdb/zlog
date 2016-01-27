#include <iostream>
#include <rados/librados.hpp>
#include "libzlog.hpp"

static void print_history(zlog::LogHL::Stream *stream, int len = 10)
{
    std::cout << "stream " << stream->Id() << ": ";
    std::vector<uint64_t> history = stream->History();
    if (history.empty())
      std::cout << "empty";
    else {
      int i = 0;
      for (auto it = history.crbegin();
          i < 10 && it != history.crend();
          i++, it++) {
        std::cout << *it << " ";
      }
    }
    std::cout << std::endl;
}

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
  ret = cluster.ioctx_create("rbd", ioctx);
  assert(ret == 0);

  zlog::SeqrClient *client;
  client = new zlog::SeqrClient("localhost", "5678");
  client->Connect();

  zlog::LogHL *log;
  ret = zlog::LogHL::OpenOrCreate(ioctx, "log2", client, &log);
  assert(ret == 0);

  std::vector<zlog::LogHL::Stream*> stream(10);
  for (unsigned i = 0; i < 10; i++) {
    ret = log->OpenStream(i, &stream[i]);
    assert(ret == 0);

    ret = stream[i]->Sync();
    assert(ret == 0);

    print_history(stream[i]);
  }

  const unsigned print_freq = 100;
  for (unsigned count = 1; 1; count++) {
    for (unsigned i = 0; i < 10; i++) {
      ceph::bufferlist bl;
      ret = stream[i]->Append(bl);
      assert(ret == 0);

      if (count % print_freq == 0) {
        ret = stream[i]->Sync();
        assert(ret == 0);
        print_history(stream[i]);
      }
    }
  }

  for (unsigned i = 0; i < 10; i++) {
    delete stream[i];
  }

  delete log;
}
