#pragma once
#include "storage/test_backend.h"
#include "zlog/log.h"

class LibZLogTest : public BackendTest {
 protected:
  void SetUp() override;
  void TearDown() override;

  zlog::Log *log = nullptr;
};
