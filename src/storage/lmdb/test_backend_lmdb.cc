#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/lmdb.h"
#include "port/stack_trace.h"
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <limits.h>

struct DBPathContext {
  char *dbpath = nullptr;
  virtual ~DBPathContext() {
    if (dbpath) {
      struct stat st;
      if (stat(dbpath, &st) == 0) {
        char cmd[PATH_MAX];
        sprintf(cmd, "rm -rf %s", dbpath);
        EXPECT_EQ(system(cmd), 0);
      }
      free(dbpath);
    }
  }
};

struct BackendTest::Context : public DBPathContext {
};

std::unique_ptr<zlog::Backend> BackendTest::create_minimal_backend()
{
  return std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
      new zlog::storage::lmdb::LMDBBackend());
}

void BackendTest::SetUp() {
  context = new Context;

  context->dbpath = strdup("/tmp/zlog.db.XXXXXX");
  ASSERT_NE(mkdtemp(context->dbpath), nullptr);
  ASSERT_GT(strlen(context->dbpath), (unsigned)0);

  auto be = std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
      new zlog::storage::lmdb::LMDBBackend());
  be->Init(context->dbpath);
  backend = std::move(be);
}

void BackendTest::TearDown() {
  backend.reset();
  if (context)
    delete context;
}

struct ZLogTest::Context : public DBPathContext {
};

void ZLogTest::DoSetUp() {
  context = new Context;

  context->dbpath = strdup("/tmp/zlog.db.XXXXXX");
  ASSERT_NE(mkdtemp(context->dbpath), nullptr);
  ASSERT_GT(strlen(context->dbpath), (unsigned)0);

  if (lowlevel()) {
    ASSERT_TRUE(exclusive());
    auto backend = std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
        new zlog::storage::lmdb::LMDBBackend());
    backend->Init(context->dbpath);
    options.backend = std::move(backend);
    options.create_if_missing = true;
    options.error_if_exists = true;
    int ret = zlog::Log::Open(options, "mylog", &log);
    ASSERT_EQ(ret, 0);
  } else {
    std::string host = "";
    std::string port = "";
    if (exclusive()) {
    } else {
      assert(0);
      host = "localhost";
      port = "5678";
    }
    options.backend_name = "lmdb";
    options.backend_options = {
      {"path", context->dbpath}
    };
    options.create_if_missing = true;
    options.error_if_exists= true;
    //options.seq_host = host;
    //options.seq_port = port;
    int ret = zlog::Log::Open(options, "mylog", &log);
    ASSERT_EQ(ret, 0);
  }
}

void ZLogTest::TearDown() {
  if (log)
    delete log;
  if (context)
    delete context;
}

int ZLogTest::reopen()
{
  // close the current log before creating a new one. otherwise civetweb
  // complains about a bunch of stuff like ports being reused.
  if (log)
    delete log;

  zlog::Log *new_log = nullptr;

  if (lowlevel()) {
    auto backend = std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
        new zlog::storage::lmdb::LMDBBackend());
    backend->Init(context->dbpath);
    options.backend = std::move(backend);
    options.create_if_missing = false;
    options.error_if_exists = false;
    int ret = zlog::Log::Open(options, "mylog", &new_log);
    if (ret)
      return ret;
  } else {
    std::string host = "";
    std::string port = "";
    if (exclusive()) {
    } else {
      assert(0);
      host = "localhost";
      port = "5678";
    }
    options.backend_name = "lmdb";
    options.backend_options = {
      {"path", context->dbpath}
    };
    options.create_if_missing = false;
    options.error_if_exists = false;
    //options.seq_host = host;
    //options.seq_port = port;
    int ret = zlog::Log::Open(options, "mylog", &new_log);
    if (ret)
      return ret;
  }

  log = new_log;
  return 0;
}

std::string ZLogTest::backend()
{
  return "lmdb";
}

#if 0

struct LibZLogCAPITest::Context : public DBPathContext {
};

void LibZLogCAPITest::SetUp() {
  context = new Context;

  context->dbpath = strdup("/tmp/zlog.db.XXXXXX");
  ASSERT_NE(mkdtemp(context->dbpath), nullptr);
  ASSERT_GT(strlen(context->dbpath), (unsigned)0);

  ASSERT_FALSE(lowlevel());

  std::string host = "";
  std::string port = "";
  if (exclusive()) {
  } else {
    host = "localhost";
    port = "5678";
  }

  const char *keys[] = {"path"};
  const char *vals[] = {context->dbpath};
  int ret = zlog_create(&options, "lmdb", "c_mylog",
      keys, vals, 1, host.c_str(), port.c_str(), &log);
  ASSERT_EQ(ret, 0);
}

void LibZLogCAPITest::TearDown() {
  if (log)
    zlog_destroy(log);

  if (context)
    delete context;
}

#endif

INSTANTIATE_TEST_CASE_P(Level, ZLogTest,
    ::testing::Values(
      std::make_tuple(true, true),
      std::make_tuple(false, true)));

INSTANTIATE_TEST_CASE_P(Level, LibZLogTest,
    ::testing::Values(
      std::make_tuple(true, true),
      std::make_tuple(false, true)));

//INSTANTIATE_TEST_CASE_P(LevelCAPI, LibZLogCAPITest,
//    ::testing::Values(
//      std::make_tuple(false, true),
//      std::make_tuple(false, false)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  int ret = RUN_ALL_TESTS();
  return ret;
}
