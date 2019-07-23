#include <numeric>
#include <deque>
#include "libzlog/log_impl.h"
#include "test_libzlog.h"

// TODO
//  - add async tests. though currently all of the synchronous apis are built on
//  top of the async versions.

TEST_P(LibZLogTest, OpenClose) {
  // TODO: we should... reverify this is true for at least ceph
  if (backend() != "lmdb") {
    std::cout << "OpenClose test not enabled for "
      << backend() << " backend" << std::endl;
    return;
  }

  const std::string input = "oh the input";

  uint64_t pos;
  int ret = log->Append(input, &pos);
  ASSERT_EQ(ret, 0);

  // TODO: after the append, if a position was faulted into a new view it means
  // we would contact the sequencer again during the retry. we could optimize
  // this by reusing the first sequence, assuming the seq didn't change. but
  // that can be future work. in the general case we probably need to also make
  // these tests more robust.
  ASSERT_GE(pos, (uint64_t)0);

  // destroy log client and reopen
  ret = reopen();
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(tail, pos+1);

  std::string output;
  ret = log->Read(tail - 1, &output);
  ASSERT_EQ(ret, 0);

  ret = log->Read(tail - 1, &output);
  ASSERT_EQ(ret, 0);

  ret = log->Read(tail - 1, &output);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(input, output);
}

/*
 * Use a log name other than `mylog` below because the test fixture
 * automatically creates a log with that name before the test is run. The other
 * option would be to expose an interface for creating a log that is called
 * explicitly by a test. That might be a good option!
 */
//TEST_P(LibZLogTest, Create) {
//  zlog::Log *log = NULL;
//
//  int ret = zlog::Log::Create(backend.get(), "", NULL, &log);
//  ASSERT_EQ(ret, -EINVAL);
//  ASSERT_EQ(log, nullptr);
//
//  ret = zlog::Log::Create(backend.get(), "mylog2", NULL, &log);
//  ASSERT_EQ(ret, 0);
//  ASSERT_NE(log, nullptr);
//
//  delete log;
//  log = NULL;
//
//  ret = zlog::Log::Create(backend.get(), "mylog2", NULL, &log);
//  ASSERT_EQ(ret, -EEXIST);
//  ASSERT_EQ(log, nullptr);
//}
//
//TEST_P(LibZLogTest, Open) {
//  zlog::Log *log = NULL;
//
//  int ret = zlog::Log::Open(backend.get(), "", NULL, &log);
//  ASSERT_EQ(ret, -EINVAL);
//  ASSERT_EQ(log, nullptr);
//
//  ret = zlog::Log::Open(backend.get(), "dne", NULL, &log);
//  ASSERT_EQ(ret, -ENOENT);
//  ASSERT_EQ(log, nullptr);
//
//  ret = zlog::Log::Create(backend.get(), "mylog2", NULL, &log);
//  ASSERT_EQ(ret, 0);
//  ASSERT_NE(log, nullptr);
//
//  delete log;
//  log = NULL;
//
//  ret = zlog::Log::Open(backend.get(), "mylog2", NULL, &log);
//  ASSERT_EQ(ret, 0);
//  ASSERT_NE(log, nullptr);
//
//  delete log;
//}

TEST_P(LibZLogTest, CheckTail) {
  uint64_t pos;
  int ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);
}

TEST_P(LibZLogTest, TrimPastEnd) {
  int ret = log->Trim(1000);
  ASSERT_EQ(ret, 0);
}

TEST_P(LibZLogTest, Append) {
  // this basic test does a series and also checks if checktail is returning an
  // updated tail. we do an append here first because it may be that internally
  // on a new log instance there is no initial mapping for the first position.
  // this means that we propose a new view that maps the position, resulting in
  // two tail increments. originally we assumed that checktail would initially
  // return zero and the first append would return zero.
  //
  // one way to make this test cleaner is to add a log interface that does like
  // like "wait_for_active(positino)" or something like that.
  //
  // actually while the appends are occuring any time a stripe fills up this can
  // occur. so really the test needs to be a bit more robust.
  uint64_t pos;
  int ret = log->Append(std::string(), &pos);
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 30; i++) {
    ret = log->Append(std::string(), &pos);
    ASSERT_EQ(ret, 0);

    ASSERT_EQ(pos, tail);

    ret = log->CheckTail(&tail);
    ASSERT_EQ(ret, 0);
  }

  uint64_t pos2;
  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);

  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  ret = log->Append(std::string(), &pos2);
  ASSERT_EQ(ret, 0);
  ASSERT_GT(pos2, pos);
}

TEST_P(LibZLogTest, Fill) {
  int ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log->Append(std::string(), &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, -EROFS);

  // ok to fill a trimmed position
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, 0);
}

TEST_P(LibZLogTest, Read) {
  std::string entry;
  int ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENOENT);

  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENODATA);

  ret = log->Read(232, &entry);
  ASSERT_EQ(ret, -ENOENT);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Read(232, &entry);
  ASSERT_EQ(ret, -ENODATA);

  const char *input = "asdfasdfasdf";
  uint64_t pos;
  ret = log->Append(input, &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, 0);

  ASSERT_TRUE(input == entry);

  // trim a written position
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);
  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, -ENODATA);

  // same for unwritten position
  pos = 456;
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);
  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, -ENODATA);
}

TEST_P(LibZLogTest, Trim) {
  // can trim empty spot
  int ret = log->Trim(55);
  ASSERT_EQ(ret, 0);

  // can trim filled spot
  ret = log->Fill(60);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(60);
  ASSERT_EQ(ret, 0);

  // can trim written spot
  uint64_t pos;
  ret = log->Append(std::string(), &pos);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  // can trim trimmed spot
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
}

// empty log: trim to first pos first stripe
TEST_P(ZLogTest, TrimTo_EmptyA) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);

  std::string entry;
  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENODATA);
  ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);
  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(0);
  ASSERT_EQ(ret, 0);
}

// empty log: trim to last pos first sub-stripe
TEST_P(ZLogTest, TrimTo_EmptyB) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(4);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 4; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 5; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to first pos last sub-stripe
TEST_P(ZLogTest, TrimTo_EmptyC) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(95);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 95; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 96; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to last pos last sub-stripe
TEST_P(ZLogTest, TrimTo_EmptyD) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(99);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 99; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 100; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to first pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_EmptyE) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(100);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 100; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 101; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to last pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_EmptyF) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(104);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 104; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 105; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to first pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_EmptyG) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(195);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 195; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 196; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to last pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_EmptyH) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(199);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 199; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 200; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to first pos first sub-stripe 3rd stripe
TEST_P(ZLogTest, TrimTo_EmptyI) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(200);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 200; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 201; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to mid point
TEST_P(ZLogTest, TrimTo_EmptyJ) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(3);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 3; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 4; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// empty log: trim to mid point
TEST_P(ZLogTest, TrimTo_EmptyK) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();

  int ret = log->trimTo(38);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 38; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 39; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }
}

// log: trim to first pos first stripe
TEST_P(ZLogTest, TrimTo_NonEmptyA) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i < 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);

  std::string entry;
  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENODATA);
  ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);
  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(0);
  ASSERT_EQ(ret, 0);

  ret = log->Read(1, &entry);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(entry, "asdf");

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to last pos first sub-stripe
TEST_P(ZLogTest, TrimTo_NonEmptyB) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(4);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 4; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 5; i <= 42; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 43; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to first pos last sub-stripe
TEST_P(ZLogTest, TrimTo_NonEmptyC) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(95);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 95; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 96; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    if (i == 0) {
      // trimming to 95 means the first object is the stripe is fully trimmed
      ASSERT_EQ(size, 0u);
    } else {
      ASSERT_GT(size, 0u);
    }
  }
}

// log: trim to last pos last sub-stripe
TEST_P(ZLogTest, TrimTo_NonEmptyD) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(99);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 99; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 100; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to first pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyE) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(100);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 100; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 101; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to last pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyF) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(104);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 104; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 105; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to first pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyG) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(195);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 195; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 196; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to last pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyH) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(199);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 199; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 200; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to first pos first sub-stripe 3rd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyI) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(200);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 200; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 201; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    // now we should have GC'd all the objects in the stripe
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to mid point
TEST_P(ZLogTest, TrimTo_NonEmptyJ) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(3);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 3; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 4; i <= 42; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 43; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to mid point
TEST_P(ZLogTest, TrimTo_NonEmptyK) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 42; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(37);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 37; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 38; i <= 42; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 43; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// appending up into second stripe before trimming
TEST_P(ZLogTest, TrimTo_NonEmptyA_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i < 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);

  std::string entry;
  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENODATA);
  ret = log->trimTo(0);
  ASSERT_EQ(ret, 0);
  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(0);
  ASSERT_EQ(ret, 0);

  ret = log->Read(1, &entry);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(entry, "asdf");

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to last pos first sub-stripe
TEST_P(ZLogTest, TrimTo_NonEmptyB_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(4);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 4; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 5; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

TEST_P(ZLogTest, TrimTo_NonEmptyC_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(95);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 95; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 96; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    if (i == 0) {
      // trimming to 95 means the first object is the stripe is fully trimmed
      ASSERT_EQ(size, 0u);
    } else {
      ASSERT_GT(size, 0u);
    }
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to last pos last sub-stripe
TEST_P(ZLogTest, TrimTo_NonEmptyD_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(99);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 99; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 100; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to first pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyE_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(100);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 100; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 101; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to last pos first sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyF_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(104);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 104; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 105; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to first pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyG_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(195);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 195; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 196; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    if (i == 100) {
      ASSERT_EQ(size, 0u);
    } else {
      ASSERT_GT(size, 0u);
    }
  }
}

// log: trim to last pos last sub-stripe 2nd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyH_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(199);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 199; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 200; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to first pos first sub-stripe 3rd stripe
TEST_P(ZLogTest, TrimTo_NonEmptyI_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(200);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 200; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 201; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(size, 0u);
  }
}

// log: trim to mid point
TEST_P(ZLogTest, TrimTo_NonEmptyJ_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(3);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 3; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 4; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

// log: trim to mid point
TEST_P(ZLogTest, TrimTo_NonEmptyK_A) {
  options.stripe_width = 5;
  options.stripe_slots = 20;
  DoSetUp();
  auto *li = (zlog::LogImpl*)log;

  for (unsigned i = 0; i <= 142; i++) {
    std::string entry = "asdf";
    int ret = log->Append(entry, nullptr);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  int ret = log->trimTo(37);
  ASSERT_EQ(ret, 0);

  for (unsigned i = 0; i <= 37; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, -ENODATA);
    ret = log->trimTo(i);
    ASSERT_EQ(ret, 0);
    ret = log->Fill(i);
    ASSERT_EQ(ret, 0);
    // TODO: are we short circuting this without I/O?
    ret = log->Trim(i);
    ASSERT_EQ(ret, 0);
  }

  for (unsigned i = 38; i <= 142; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(entry, "asdf");
  }

  for (unsigned i = 143; i < 300; i++) {
    std::string entry;
    ret = log->Read(i, &entry);
    // TODO: this is related to reading past eol
    ASSERT_EQ(ret, -ENOENT);
  }

  for (unsigned i = 0; i < 5; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }

  for (unsigned i = 100; i < 105; i++) {
    auto oid = li->view_mgr->map(li->view_mgr->view(), i);
    ASSERT_TRUE(oid);
    size_t size;
    int ret = li->backend->Stat(*oid, &size);
    ASSERT_EQ(ret, 0);
    ASSERT_GT(size, 0u);
  }
}

TEST_P(LibZLogCAPITest, Trim) {
  // can trim empty spot
  int ret = zlog_trim(log, 55);
  ASSERT_EQ(ret, 0);

  // can trim filled spot
  ret = zlog_fill(log, 60);
  ASSERT_EQ(ret, 0);
  ret = zlog_trim(log, 60);
  ASSERT_EQ(ret, 0);

  // can trim written spot
  uint64_t pos;
  char data[5];
  ret = zlog_append(log, data, sizeof(data), &pos);
  ASSERT_EQ(ret, 0);
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);

  // can trim trimmed spot
  ret = zlog_trim(log, 70);
  ASSERT_EQ(ret, 0);
  ret = zlog_trim(log, 70);
  ASSERT_EQ(ret, 0);
}

TEST_P(LibZLogCAPITest, TrimTo) {
  int ret = zlog_trim_to(log, 55);
  ASSERT_EQ(ret, 0);
}

TEST_P(LibZLogCAPITest, CheckTail) {
  uint64_t pos;
  int ret = zlog_checktail(log, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = zlog_checktail(log, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);
}

TEST_P(LibZLogCAPITest, Append) {
  uint64_t tail;
  int ret = zlog_checktail(log, &tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 100; i++) {
    char data[1];
    uint64_t pos;
    ret = zlog_append(log, data, sizeof(data), &pos);
    ASSERT_EQ(ret, 0);

    ASSERT_EQ(pos, tail);

    ret = zlog_checktail(log, &tail);
    ASSERT_EQ(ret, 0);
  }

  uint64_t pos, pos2;
  ret = zlog_checktail(log, &pos);
  ASSERT_EQ(ret, 0);

  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);

  char data[1];
  ret = zlog_append(log, data, sizeof(data), &pos2);
  ASSERT_EQ(ret, 0);
  ASSERT_GT(pos2, pos);
}

TEST_P(LibZLogCAPITest, Fill) {
  int ret = zlog_fill(log, 0);
  ASSERT_EQ(ret, 0);

  ret = zlog_fill(log, 232);
  ASSERT_EQ(ret, 0);

  ret = zlog_fill(log, 232);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  char data[1];
  ret = zlog_append(log, data, sizeof(data), &pos);
  ASSERT_EQ(ret, 0);

  ret = zlog_fill(log, pos);
  ASSERT_EQ(ret, -EROFS);

  // ok to fill a trimmed position
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);

  ret = zlog_fill(log, pos);
  ASSERT_EQ(ret, 0);
}

TEST_P(LibZLogCAPITest, Read) {
  char data[1024];

  int ret = zlog_read(log, 0, data, sizeof(data));
  ASSERT_EQ(ret, -ENOENT);

  ret = zlog_fill(log, 0);
  ASSERT_EQ(ret, 0);

  ret = zlog_read(log, 0, data, sizeof(data));
  ASSERT_EQ(ret, -ENODATA);

  ret = zlog_read(log, 232, data, sizeof(data));
  ASSERT_EQ(ret, -ENOENT);

  ret = zlog_fill(log, 232);
  ASSERT_EQ(ret, 0);

  ret = zlog_read(log, 232, data, sizeof(data));
  ASSERT_EQ(ret, -ENODATA);

  const char *s = "asdfasdfasdfasdfasdfasdf";

  uint64_t pos;
  memset(data, 0, sizeof(data));
  sprintf(data, "%s", s);
  ret = zlog_append(log, data, sizeof(data), &pos);
  ASSERT_EQ(ret, 0);

  char data2[1024];
  memset(data2, 0, sizeof(data2));
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ((unsigned)ret, sizeof(data2));

  ASSERT_TRUE(strcmp(data2, s) == 0);

  // trim a written position
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ(ret, -ENODATA);

  // same for unwritten position
  pos = 456;
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ(ret, -ENODATA);
}
