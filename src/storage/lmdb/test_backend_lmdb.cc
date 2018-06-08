#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/lmdb.h"
#include "port/stack_trace.h"
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <limits.h>
#include <google/protobuf/stubs/common.h>

void BackendTest::SetUp() {}
void BackendTest::TearDown() {}

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

struct LibZLogTest::Context : public DBPathContext {
};

void LibZLogTest::SetUp() {
  context = new Context;

  context->dbpath = strdup("/tmp/zlog.db.XXXXXX");
  ASSERT_NE(mkdtemp(context->dbpath), nullptr);
  ASSERT_GT(strlen(context->dbpath), (unsigned)0);

  if (lowlevel()) {
    ASSERT_TRUE(exclusive());
    auto backend = std::unique_ptr<zlog::storage::lmdb::LMDBBackend>(
        new zlog::storage::lmdb::LMDBBackend());
    backend->Init(context->dbpath);
    int ret = zlog::Log::CreateWithBackend(options,
        std::move(backend), "mylog", &log);
    ASSERT_EQ(ret, 0);
  } else {
    std::string host = "";
    std::string port = "";
    if (exclusive()) {
    } else {
      host = "localhost";
      port = "5678";
    }
    int ret = zlog::Log::Create(options, "lmdb", "mylog",
        {{"path", context->dbpath}}, host, port, &log);
    ASSERT_EQ(ret, 0);
  }
}

void LibZLogTest::TearDown() {
  if (log)
    delete log;
  if (context)
    delete context;
}

int LibZLogTest::reopen()
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
    int ret = zlog::Log::OpenWithBackend(options,
        std::move(backend), "mylog", &new_log);
    if (ret)
      return ret;
  } else {
    std::string host = "";
    std::string port = "";
    if (exclusive()) {
    } else {
      host = "localhost";
      port = "5678";
    }
    int ret = zlog::Log::Open(options, "lmdb", "mylog",
        {{"path", context->dbpath}}, host, port, &new_log);
    if (ret)
      return ret;
  }

  log = new_log;
  return 0;
}

std::string LibZLogTest::backend()
{
  return "lmdb";
}

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

INSTANTIATE_TEST_CASE_P(Level, LibZLogTest,
    ::testing::Values(
      std::make_tuple(true, true),
      std::make_tuple(false, true),
      std::make_tuple(false, false)));

INSTANTIATE_TEST_CASE_P(LevelCAPI, LibZLogCAPITest,
    ::testing::Values(
      std::make_tuple(false, true),
      std::make_tuple(false, false)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  int ret = RUN_ALL_TESTS();
  google::protobuf::ShutdownProtobufLibrary();
  return ret;
}
