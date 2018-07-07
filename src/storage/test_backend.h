#pragma once
#include <memory>
#include "zlog/backend.h"
#include "zlog/options.h"
#include "gtest/gtest.h"

class BackendTest : public ::testing::Test {
 protected:
  struct Context;

  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<zlog::Backend> backend;
  Context *context = nullptr;
};
