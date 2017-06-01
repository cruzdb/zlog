#include <sstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <cstdlib>
#include <time.h>
#include <sys/time.h>
#include "zlog/db.h"
#include "zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

#if __APPLE__
static inline uint64_t getns()
{
  struct timeval tv;
  assert(gettimeofday(&tv, NULL) == 0);
  uint64_t res = tv.tv_sec * 1000000000ULL;
  return res + tv.tv_usec * 1000ULL;
}
#else
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
#endif

static inline std::string tostr(int value)
{
  std::stringstream ss;
  ss << std::setw(9) << std::setfill('0') << value;
  return ss.str();
}

int main(int argc, char **argv)
{
  int stop_after = 0;
  if (argc > 1) {
    stop_after = atoi(argv[1]);
  }

  auto client = new FakeSeqrClient();
  auto be = new LMDBBackend("fakepool");
  be->Init("/tmp/zlog-db", false);

  zlog::Log *log;
  int ret = zlog::Log::OpenOrCreate(be, "log", client, &log);
  assert(ret == 0);

  client->Init(log, "fakepool", "log");

  DB *db;
  ret = DB::Open(log, true, &db);
  assert(ret == 0);

  std::srand(0);

  uint64_t txn_count = 0;
  int total_txn_count = 0;
  uint64_t start_ns = getns();

  int x = 0;
  while (true) {
    auto txn = db->BeginTransaction();
    int nkey = x++;//std::rand();
    const std::string key = tostr(nkey);
    txn->Put(key, key);
    txn->Commit();
    delete txn;

    if (++txn_count == 2000) {
      uint64_t dur_ns = getns() - start_ns;
      double iops = (double)(txn_count * 1000000000ULL) / (double)dur_ns;
      std::cout << "sha1 dev-backend hostname: iops " << iops << std::endl;
      std::cout << "validating tree..." << std::flush;
      //db->validate();
      std::cout << " done" << std::endl << std::flush;
      txn_count = 0;
      start_ns = getns();
    }

    total_txn_count++;
    if (stop_after  && total_txn_count >= stop_after)
      break;
  }

  delete db;
  delete log;
  delete client;
  be->Close();
  delete be;
}
