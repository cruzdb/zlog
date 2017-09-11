#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

struct Context {
  char *dbpath;
};

void BackendTest::SetUp() {
  auto c = std::unique_ptr<Context>(new Context);

  c->dbpath = strdup("/tmp/zlog.db.XXXXXX");
  c->dbpath = mkdtemp(c->dbpath);
  assert(c->dbpath);

  auto b = std::unique_ptr<LMDBBackend>(new LMDBBackend());
  b->Init(c->dbpath, true);

  be = b.release();
  be_ctx = c.release();
}

void BackendTest::TearDown() {
  //be->Close();
  //delete be;
}

void LibZLogTest::SetUp() {
  //BackendTest::SetUp();
  //auto client = new FakeSeqrClient();
}

void LibZLogTest::TearDown() {
  //BackendTest::TearDown();
  //delete client;
  //char cmd[64];
  //sprintf(cmd, "rm -rf %s", dbpath);
  //system(cmd);
  //free(dbpath);
}
