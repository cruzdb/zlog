#include <memory>
#include <unistd.h>
#include "zlog/backend/ram.h"
#include "zlog/options.h"
#include "zlog/log.h"

int main(int argc, char **argv)
{
  auto backend = std::unique_ptr<zlog::storage::ram::RAMBackend>(
      new zlog::storage::ram::RAMBackend());

  zlog::Options options;
  options.backend = std::move(backend);
  options.create_if_missing = true;
  options.error_if_exists = true;

  zlog::Log *log;
  int ret = zlog::Log::Open(options, "mylog", &log);
  assert(ret == 0);

#if 0
  for (int i = 0; i < 100000; i++) {
    uint64_t pos;
    int ret = log->Append("data", &pos);
    assert(ret == 0);
    std::cout << pos << std::endl;
  }
#else
  std::mutex lock;
  for (int i = 0; i < 50000; i++) {
    int ret = log->appendAsync("data", [&](int ret, uint64_t pos) {
      std::lock_guard<std::mutex> lk(lock);
      std::cout << pos << " " << ret << std::endl;
    });
    assert(ret == 0);
  }
#endif

  // will wait for async ops to run callbacks
  std::cout << "done looping" << std::endl;
  sleep(3);
  std::cout << "done sleeping" << std::endl;
  delete log;

  return 0;
}
