#include <sstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <cstdlib>
#include <time.h>
#include "zlog/db.h"
#include "zlog/backend/ram.h"

static inline uint64_t __getns(clockid_t clock)
{
  struct timespec ts;
  int ret = clock_gettime(clock, &ts);
  assert(ret == 0);
  return (((uint64_t)ts.tv_sec) * 1000000000ULL) + ts.tv_nsec;
}

static inline uint64_t getns()
{
  return __getns(CLOCK_MONOTONIC);
}

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(3) << std::setfill('0') << value;
  return ss.str();
}

int main(int argc, char **argv)
{
    zlog::Log *log;
    auto be = new RAMBackend();
    auto client = new FakeSeqrClient();
    int ret = zlog::Log::Create(be, "log", client, &log);
    assert(ret == 0);

    DB *db;
    ret = DB::Open(log, true, &db);
    assert(ret == 0);

    uint64_t txn_count = 0;
    uint64_t start_ns = getns();
    while (true) {
      auto txn = db->BeginTransaction();
      int nkey = std::rand();
      const std::string key = tostr(nkey);
      txn->Put(key, key);
      txn->Commit();
      delete txn;

      if (++txn_count == 2000) {
        uint64_t dur_ns = getns() - start_ns;
        double iops = (double)(txn_count * 1000000000ULL) / (double)dur_ns;
        std::cout << "sha1 dev-backend hostname: iops " << iops << std::endl;
        std::cout << "validating tree..." << std::flush;
        db->validate();
        std::cout << " done" << std::endl << std::flush;
        txn_count = 0;
        start_ns = getns();
      }
    }

    delete db;
    delete log;
    delete client;
    delete be;
}
