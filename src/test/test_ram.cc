#include <gtest/gtest.h>
#include <deque>
#include "include/zlog/log.h"
#include "include/zlog/ram_backend.h"

class LibZlog : public ::testing::Test {
 public:
  void SetUp() {
    be = new RAMBackend();
  }

  void TearDown() {
    delete be;
  }

  Backend  *be;
};

class LibZlogStream : public LibZlog {};

// common tests
#include "test.cc"
