#pragma once
#include "storage/test_backend.h"
#include "zlog/log.h"

class LibZLogTest : public BackendTest {
 protected:
  class Context;

  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<zlog::Log> log;
  Context *context = nullptr;
};
