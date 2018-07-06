#include <zlog/log.h>
#include <iostream>

int main(int argc, char **argv)
{
  zlog::Options options;
  zlog::Log *log;
  int ret = zlog::Log::Open(options, "lmdb", "mylog",
      {{"path", "/tmp/zlog.tmp.db"}}, "", "", &log);
  assert(ret == 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  assert(ret == 0);
  (void)ret;

  std::string output;
  ret = log->Read(tail-1, &output);
  assert(ret == 0);

  std::cout << output << std::endl;

  delete log;

  return 0;
}
