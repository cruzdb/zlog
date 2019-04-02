#pragma once
#include <tuple>
#include "gtest/gtest.h"
#include "zlog/log.h"
#include "zlog/capi.h"

// C++ API
class ZLogTest : public ::testing::TestWithParam<std::tuple<bool, bool>> {
 protected:
  struct Context;

  void DoSetUp();
  void TearDown() override;

  zlog::Log *log = nullptr;
  Context *context = nullptr;
  zlog::Options options;

  int reopen();

  std::string backend();

  bool lowlevel() {
    return std::get<0>(GetParam());
  }

  bool exclusive() {
    return std::get<1>(GetParam());
  }
};

class LibZLogTest : public ZLogTest {
 protected:
  void SetUp() override {
    DoSetUp();
  }
};

// C API
class LibZLogCAPITest : public ::testing::TestWithParam<std::tuple<bool, bool>> {
 protected:
  struct Context;

  void SetUp() override;
  void TearDown() override;

  zlog_log_t log = nullptr;
  Context *context = nullptr;
  zlog::Options options;

  bool lowlevel() {
    return std::get<0>(GetParam());
  }

  bool exclusive() {
    return std::get<1>(GetParam());
  }
};
