#pragma once
#include "zlog/backend.h"
#include "gtest/gtest.h"

class BackendTest : public ::testing::Test {
 protected:
  void SetUp() override;
  void TearDown() override;

  Backend *be = nullptr;
  void *be_ctx;
};
