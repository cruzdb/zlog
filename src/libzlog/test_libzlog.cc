#include <numeric>
#include <deque>
#include "test_libzlog.h"
#include "zlog/stream.h"

struct aio_state {
  zlog::AioCompletion *c;
  uint64_t position;
  int retval;

  std::string in_data;
  std::string out_data;
};

static void handle_aio_cb(aio_state *ctx)
{
  ctx->retval = ctx->c->ReturnValue();
}

static void handle_aio_cb_read(aio_state *ctx)
{
  ctx->retval = ctx->c->ReturnValue();
}

TEST_P(LibZLogTest, OpenClose) {
  // TODO: we should... reverify this is true for at least ceph
  if (backend() != "lmdb") {
    std::cout << "OpenClose test not enabled for "
      << backend() << " backend" << std::endl;
    return;
  }

  const std::string input = "oh the input";

  uint64_t pos;
  int ret = log->Append(zlog::Slice(input), &pos);
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

TEST_P(LibZLogTest, Aio) {
  // issue some appends
  std::vector<aio_state*> aios;
  for (int i = 0; i < 1; i++) {
    auto ctx = new aio_state;
    ctx->position = (uint64_t)-1;
    ctx->retval = -1;
    std::stringstream ss;
    ss << "data." << i;
    ctx->in_data = ss.str();
    ASSERT_NE(ctx->in_data, ctx->out_data);
    ctx->c = zlog::Log::aio_create_completion(
        std::bind(handle_aio_cb, ctx));
    int ret = log->AioAppend(ctx->c, zlog::Slice(ctx->in_data), &ctx->position);
    ASSERT_EQ(ret, 0);
    aios.push_back(ctx);
  }

  // wait for them to complete
  for (auto ctx : aios) {
    ctx->c->WaitForComplete();
    ASSERT_GE(ctx->position, (uint64_t)0);
    ASSERT_EQ(ctx->retval, 0);
    delete ctx->c;
    ctx->c = NULL;
  }

  // re-read and verify
  for (auto ctx : aios) {
    ctx->c = zlog::Log::aio_create_completion(
        std::bind(handle_aio_cb_read, ctx));
    int ret = log->AioRead(ctx->position, ctx->c, &ctx->out_data);
    ASSERT_EQ(ret, 0);
  }

  // wait for them to complete
  for (auto ctx : aios) {
    ctx->c->WaitForComplete();
    ASSERT_GE(ctx->position, (uint64_t)0);
    ASSERT_EQ(ctx->retval, 0);
    ASSERT_EQ(ctx->in_data, ctx->out_data);
    delete ctx->c;
    delete ctx;
  }
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
  int ret = log->Append(zlog::Slice(), &pos);
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 30; i++) {
    ret = log->Append(zlog::Slice(), &pos);
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

  ret = log->Append(zlog::Slice(), &pos2);
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
  ret = log->Append(zlog::Slice(), &pos);
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
  ret = log->Append(zlog::Slice(input), &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, 0);

  ASSERT_TRUE(zlog::Slice(input) == zlog::Slice(entry));

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
  ret = log->Append(zlog::Slice(), &pos);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  // can trim trimmed spot
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
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

//TEST_P(LibZLogCAPITest, Create) {
//  zlog_log_t log2;
//
//  int ret = zlog_create(c_backend, "", NULL, &log2);
//  ASSERT_EQ(ret, -EINVAL);
//
//  ret = zlog_create(c_backend, "mylog3", NULL, &log2);
//  ASSERT_EQ(ret, 0);
//
//  ret = zlog_destroy(log2);
//  ASSERT_EQ(ret, 0);
//
//  ret = zlog_create(c_backend, "mylog3", NULL, &log2);
//  ASSERT_EQ(ret, -EEXIST);
//}
//
//TEST_P(LibZLogCAPITest, Open) {
//  zlog_log_t log2;
//
//  int ret = zlog_open(c_backend, "", NULL, &log2);
//  ASSERT_EQ(ret, -EINVAL);
//
//  ret = zlog_open(c_backend, "dne", NULL, &log2);
//  ASSERT_EQ(ret, -ENOENT);
//
//  ret = zlog_create(c_backend, "mylog3", NULL, &log2);
//  ASSERT_EQ(ret, 0);
//  ret = zlog_destroy(log2);
//  ASSERT_EQ(ret, 0);
//
//  ret = zlog_open(c_backend, "mylog3", NULL, &log2);
//  ASSERT_EQ(ret, 0);
//  ret = zlog_destroy(log2);
//  ASSERT_EQ(ret, 0);
//}

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
