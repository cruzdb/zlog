#include <unistd.h>
#include <stdlib.h>
#include <gtest/gtest.h>
#include <numeric>
#include "include/zlog/log.h"
#include "include/zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

class LibZlog : public ::testing::Test {
 public:
  void SetUp() {
    dbpath = strdup("/tmp/zlog.db.XXXXXX");
    dbpath = mkdtemp(dbpath);
    assert(dbpath);
    be = new LMDBBackend();
    be->Init(dbpath, true);
    client = new FakeSeqrClient();
  }

  void TearDown() {
    be->Close();
    delete be;
    delete client;

    char cmd[64];
    sprintf(cmd, "rm -rf %s", dbpath);
    system(cmd);
    free(dbpath);
  }

  char *dbpath;
  LMDBBackend *be;
  zlog::SeqrClient *client;
};

class LibZlogStream : public LibZlog {};

// common tests
#include "test.cc"
