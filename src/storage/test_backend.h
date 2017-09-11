#pragma once
#include "zlog/backend.h"
#include "gtest/gtest.h"

class BackendTest : public ::testing::Test {
 protected:
  class Context;

  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<Backend> backend;
  Context *context = nullptr;
};
