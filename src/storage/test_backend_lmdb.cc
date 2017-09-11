#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

class BackendTest::Context {
 public:
  std::unique_ptr<char> dbpath;
};

class LibZLogTest::Context {
 public:
  std::unique_ptr<FakeSeqrClient> client;
};

void BackendTest::SetUp() {
  auto c = std::unique_ptr<BackendTest::Context>(new BackendTest::Context);
  c->dbpath = std::unique_ptr<char>(strdup("/tmp/zlog.db.XXXXXX"));
  mkdtemp(c->dbpath.get());
  ASSERT_GT(strlen(c->dbpath.get()), (unsigned)0);

  auto b = std::unique_ptr<LMDBBackend>(new LMDBBackend());
  b->Init(c->dbpath.get(), true);

  context = c.release();
  backend = std::move(b);
}

void BackendTest::TearDown() {
  if (backend) {
    LMDBBackend *b = (LMDBBackend*)backend.get();
    b->Close();
  }
  if (context) {
    char cmd[64];
    sprintf(cmd, "rm -rf %s", context->dbpath.get());
    system(cmd);
    delete context;
  }
}

void LibZLogTest::SetUp() {
  ASSERT_NO_FATAL_FAILURE(BackendTest::SetUp());

  auto c = std::unique_ptr<LibZLogTest::Context>(new LibZLogTest::Context);
  c->client = std::unique_ptr<FakeSeqrClient>(new FakeSeqrClient());

  zlog::Log *l;
  int ret = zlog::Log::Create(backend.get(), "mylog",
      c->client.get(), &l);
  ASSERT_EQ(ret, 0);

  log.reset(l);
  context = c.release();
}

void LibZLogTest::TearDown() {
  if (context) {
    delete context;
  }
  BackendTest::TearDown();
}
