#include "gtest/gtest.h"
#include "include/zlog/options.h"
#include "libzlog/log_backend.h"

TEST(LogBackendDeathTest, Constructor) {
  const auto be = std::shared_ptr<zlog::Backend>(
      (zlog::Backend*)0xdeadbeef, [](zlog::Backend *p) {});
  ASSERT_DEATH({
    zlog::LogBackend(nullptr, "h", "p", "s");
  }, "backend.+failed");
  ASSERT_DEATH({
    zlog::LogBackend(be, "", "p", "s");
  }, "hoid.+failed");
  ASSERT_DEATH({
    zlog::LogBackend(be, "h", "", "s");
  }, "prefix.+failed");
  ASSERT_DEATH({
    zlog::LogBackend(be, "h", "p", "");
  }, "secret.+failed");
}

TEST(LogBackendTest, Getters) {
  const auto be = std::shared_ptr<zlog::Backend>(
      (zlog::Backend*)0xdeadbeef, [](zlog::Backend *p) {});
  const auto lbe = zlog::LogBackend(be, "h", "p", "s");
  ASSERT_EQ(lbe.backend(), be);
  ASSERT_EQ(lbe.hoid(), "h");
  ASSERT_EQ(lbe.prefix(), "p");
  ASSERT_EQ(lbe.secret(), "s");
}
