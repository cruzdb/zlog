#include <gtest/gtest.h>
#include "include/zlog/log.h"
#include "include/zlog/backend/ram.h"

class LibZlog : public ::testing::Test {
 public:
  void SetUp() {
    be = new RAMBackend();
    client = new FakeSeqrClient();
  }

  void TearDown() {
    delete be;
    delete client;
  }

  Backend  *be;
  zlog::SeqrClient *client;
};

class LibZlogStream : public LibZlog {};

// common tests
#include "test.cc"
