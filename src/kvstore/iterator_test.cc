#include <sstream>
#include <iomanip>
#include "zlog/db.h"
#include "zlog/backend/ram.h"

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

  std::vector<std::string> strs{"m", "f", "t"};
  for (auto s : strs) {
    auto txn = db->BeginTransaction();
    txn->Put(s, "");
    txn->Commit();
  }

  auto it = db->NewIterator();
  assert(!it->Valid());

  // equality
  it->Seek("m");
  assert(it->Valid());
  assert(it->key() == "m");

  it->Seek("f");
  assert(it->Valid());
  assert(it->key() == "f");

  it->Seek("t");
  assert(it->Valid());
  assert(it->key() == "t");

  // edges
  it->Seek("a");
  assert(it->Valid());
  assert(it->key() == "f");

  it->Seek("h");
  assert(it->Valid());
  assert(it->key() == "m");

  it->Seek("j");
  assert(it->Valid());
  assert(it->key() == "m");

  it->Seek("o");
  assert(it->Valid());
  assert(it->key() == "t");

  it->Seek("v");
  assert(!it->Valid());

  it->Seek("x");
  assert(!it->Valid());

  return 0;
}
