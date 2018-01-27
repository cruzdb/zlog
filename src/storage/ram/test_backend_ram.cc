#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "include/zlog/backend/ram.h"
#include "port/stack_trace.h"
#include <google/protobuf/stubs/common.h>

void BackendTest::SetUp() {}
void BackendTest::TearDown() {}

void LibZLogTest::SetUp() {
  if (lowlevel()) {
    ASSERT_TRUE(exclusive());
    auto backend = std::unique_ptr<zlog::storage::ram::RAMBackend>(
        new zlog::storage::ram::RAMBackend());
    int ret = zlog::Log::CreateWithBackend(std::move(backend),
        "mylog", &log);
    ASSERT_EQ(ret, 0);
  } else {
    ASSERT_TRUE(exclusive());
    std::string host = "";
    std::string port = "";
    int ret = zlog::Log::Create("ram", "mylog", {}, host, port, &log);
    ASSERT_EQ(ret, 0);
  }
}

void LibZLogTest::TearDown() {
  if (log)
    delete log;
}

void LibZLogCAPITest::SetUp() {
  ASSERT_FALSE(lowlevel());
  ASSERT_TRUE(exclusive());

  std::string host = "";
  std::string port = "";

  int ret = zlog_create("ram", "c_mylog",
      NULL, NULL, 0, host.c_str(), port.c_str(), &log);
  ASSERT_EQ(ret, 0);
}

void LibZLogCAPITest::TearDown() {
  if (log)
    zlog_destroy(log);
}

INSTANTIATE_TEST_CASE_P(Level, LibZLogTest,
    ::testing::Values(
      std::make_tuple(true, true),
      std::make_tuple(false, true)));

INSTANTIATE_TEST_CASE_P(LevelCAPI, LibZLogCAPITest,
    ::testing::Values(
      std::make_tuple(false, true)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  int ret = RUN_ALL_TESTS();
  google::protobuf::ShutdownProtobufLibrary();
  return ret;
}
