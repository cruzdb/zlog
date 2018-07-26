#include <zlog/log.h>

int main(int argc, char **argv)
{
  zlog::Options options;
  zlog::Log *log;
  int ret = zlog::Log::Create(options, "lmdb", "mylog",
      {{"path", "/tmp/zlog.tmp.db"}}, "", "", &log);
  assert(ret == 0);
  (void)ret;

  // const std::string input = "random input";

  // uint64_t size = 1024 * 32 ;

  // for(uint64_t i = 0; i < size; i++)
  // {
  //   uint64_t pos = i;
  //   ret = log->Append(zlog::Slice(input), &pos);
  //   assert(ret == 0);
  // }
  

  delete log;

  return 0;
}
