#pragma once
#include <memory>
#include "zlog/backend.h"
#include "gtest/gtest.h"

class BackendTest : public ::testing::Test {
 protected:
  class Context;

  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<Backend> backend;
  zlog_backend_t c_backend;
  Context *context = nullptr;
};
