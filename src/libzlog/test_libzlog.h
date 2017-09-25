#pragma once
#include "gtest/gtest.h"
#include "zlog/log.h"
#include "zlog/capi.h"

// C++ API
class LibZLogTest : public ::testing::TestWithParam<bool> {
 protected:
  struct Context;

  void SetUp() override;
  void TearDown() override;

  zlog::Log *log = nullptr;
  Context *context = nullptr;

  bool lowlevel() {
    return GetParam();
  }
};

// C API
class LibZLogCAPITest : public ::testing::TestWithParam<bool> {
 protected:
  struct Context;

  void SetUp() override;
  void TearDown() override;

  zlog_log_t log = nullptr;
  Context *context = nullptr;

  bool lowlevel() {
    return GetParam();
  }
};
