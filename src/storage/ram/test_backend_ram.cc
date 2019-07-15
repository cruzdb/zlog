#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/ram.h"
#include "port/stack_trace.h"

std::unique_ptr<zlog::Backend> BackendTest::create_minimal_backend()
{
  return std::unique_ptr<zlog::storage::ram::RAMBackend>(
      new zlog::storage::ram::RAMBackend());
}

void BackendTest::SetUp() {
  backend = create_minimal_backend();
}

void BackendTest::TearDown() {
  backend.reset();
}

void ZLogTest::DoSetUp() {
  if (lowlevel()) {
    ASSERT_TRUE(exclusive());
    auto backend = std::unique_ptr<zlog::storage::ram::RAMBackend>(
        new zlog::storage::ram::RAMBackend());
    options.backend = std::move(backend);
    options.create_if_missing = true;
    options.error_if_exists = true;
    int ret = zlog::Log::Open(options, "mylog", &log);
    ASSERT_EQ(ret, 0);
  } else {
    ASSERT_TRUE(exclusive());
    std::string host = "";
    std::string port = "";
    options.create_if_missing = true;
    options.error_if_exists = true;
    options.backend_name = "ram";
    //options.seq_host = host;
    //options.seq_port = port;
    int ret = zlog::Log::Open(options, "mylog", &log);
    ASSERT_EQ(ret, 0);
  }
}

void ZLogTest::TearDown() {
  if (log)
    delete log;
}

int ZLogTest::reopen()
{
  return -EOPNOTSUPP;
}

std::string ZLogTest::backend()
{
  return "ram";
}

void LibZLogCAPITest::SetUp() {
  ASSERT_FALSE(lowlevel());
  ASSERT_TRUE(exclusive());

  std::string host = "";
  std::string port = "";

  int ret = zlog_create(&options, "ram", "c_mylog",
      NULL, NULL, 0, host.c_str(), port.c_str(), &log);
  ASSERT_EQ(ret, 0);
}

void LibZLogCAPITest::TearDown() {
  if (log)
    zlog_destroy(log);
}

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
//      std::make_tuple(false, true)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  int ret = RUN_ALL_TESTS();
  return ret;
}
