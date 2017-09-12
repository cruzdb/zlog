#pragma once
#include "storage/test_backend.h"
#include "zlog/log.h"
#include "zlog/capi.h"

class LibZLogTest : public BackendTest {
 protected:
  class Context;

  void SetUp() override;
  void TearDown() override;

  std::unique_ptr<zlog::Log> log;
  Context *context = nullptr;
  zlog_log_t c_log;
};
