#include <gtest/gtest.h>
#include <numeric>
#include "include/zlog/log.h"
#include "include/zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

class LibZlog : public ::testing::Test {
 public:
  void SetUp() {
    be = new LMDBBackend();
    be->Init();
    client = new FakeSeqrClient();
  }

  void TearDown() {
    be->Close();
    delete be;
    delete client;
  }

  LMDBBackend *be;
  zlog::SeqrClient *client;
};

class LibZlogStream : public LibZlog {};

// common tests
#include "test.cc"
