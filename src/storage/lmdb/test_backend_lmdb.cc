#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

class BackendTest::Context {
 public:
  std::unique_ptr<char> dbpath;
  std::unique_ptr<char> c_dbpath;
};

class LibZLogTest::Context {
 public:
  std::unique_ptr<FakeSeqrClient> client;
  zlog_sequencer_t c_client;
};

void BackendTest::SetUp() {
  auto c = std::unique_ptr<BackendTest::Context>(new BackendTest::Context);

  // C++ API
  c->dbpath = std::unique_ptr<char>(strdup("/tmp/zlog.db.XXXXXX"));
  mkdtemp(c->dbpath.get());
  ASSERT_GT(strlen(c->dbpath.get()), (unsigned)0);

  auto b = std::unique_ptr<LMDBBackend>(new LMDBBackend());
  b->Init(c->dbpath.get(), true);

  // C API
  c->c_dbpath = std::unique_ptr<char>(strdup("/tmp/zlog.db.XXXXXX"));
  mkdtemp(c->c_dbpath.get());
  ASSERT_GT(strlen(c->c_dbpath.get()), (unsigned)0);

  int ret = zlog_create_lmdb_backend(c->c_dbpath.get(), &c_backend);
  ASSERT_EQ(ret, 0);

  context = c.release();
  backend = std::move(b);
}

void BackendTest::TearDown() {
  if (backend) {
    LMDBBackend *b = (LMDBBackend*)backend.get();
    b->Close();

    zlog_destroy_lmdb_backend(c_backend);
  }
  if (context) {
    char cmd[64];
    sprintf(cmd, "rm -rf %s", context->dbpath.get());
    system(cmd);

    sprintf(cmd, "rm -rf %s", context->c_dbpath.get());
    system(cmd);

    delete context;
  }
}

void LibZLogTest::SetUp() {
  ASSERT_NO_FATAL_FAILURE(BackendTest::SetUp());

  // C++ API
  auto c = std::unique_ptr<LibZLogTest::Context>(new LibZLogTest::Context);
  c->client = std::unique_ptr<FakeSeqrClient>(new FakeSeqrClient());

  zlog::Log *l;
  int ret = zlog::Log::Create(backend.get(), "mylog",
      c->client.get(), &l);
  ASSERT_EQ(ret, 0);

  // C API
  ret = zlog_create_fake_sequencer(&c->c_client);
  ASSERT_EQ(ret, 0);

  ret = zlog_create(c_backend, "c_mylog", c->c_client, &c_log);
  ASSERT_EQ(ret, 0);

  log.reset(l);
  context = c.release();
}

void LibZLogTest::TearDown() {
  if (context) {
    zlog_destroy_fake_sequencer(context->c_client);
    zlog_destroy(c_log);
    delete context;
  }
  BackendTest::TearDown();
}
