#include <zlog/log.h>

int main(int argc, char **argv)
{
  zlog::Options options;
  zlog::Log *log;
  int ret = zlog::Log::Create(options, "lmdb", "mylog",
      {{"path", "/tmp/zlog.tmp.db"}}, "", "", &log);
  assert(ret == 0);

  const std::string input = "oh the input";

  uint64_t pos;
  ret = log->Append(zlog::Slice(input), &pos);
  assert(ret == 0);

  delete log;

  return 0;
}
