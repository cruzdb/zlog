#include "test_libzlog.h"

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

TEST_F(LibZLogTest, Aio) {
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
    int ret = log->AioAppend(ctx->c, Slice(ctx->in_data), &ctx->position);
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
TEST_F(LibZLogTest, Create) {
  zlog::Log *log = NULL;

  int ret = zlog::Log::Create(be, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  // TODO: creating a log with NULL seqclient should be an error
  ret = zlog::Log::Create(be, "mylog2", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::Log::Create(be, "mylog2", NULL, &log);
  ASSERT_EQ(ret, -EEXIST);
  ASSERT_EQ(log, nullptr);
}

TEST_F(LibZLogTest, Open) {
  zlog::Log *log = NULL;

  int ret = zlog::Log::Open(be, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  ret = zlog::Log::Open(be, "dne", NULL, &log);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(log, nullptr);

  ret = zlog::Log::Create(be, "mylog2", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::Log::Open(be, "mylog2", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
}

TEST_F(LibZLogTest, CheckTail) {
  uint64_t pos;
  int ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);
}

TEST_F(LibZLogTest, Append) {
  uint64_t tail;
  int ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 100; i++) {
    uint64_t pos;
    ret = log->Append(Slice(), &pos);
    ASSERT_EQ(ret, 0);

    ASSERT_EQ(pos, tail);

    ret = log->CheckTail(&tail);
    ASSERT_EQ(ret, 0);
  }

  uint64_t pos, pos2;
  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);

  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  ret = log->Append(Slice(), &pos2);
  ASSERT_EQ(ret, 0);
  ASSERT_GT(pos2, pos);
}

TEST_F(LibZLogTest, Fill) {
  int ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log->Append(Slice(), &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, -EROFS);

  // ok to fill a trimmed position
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, 0);
}

TEST_F(LibZLogTest, Read) {
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
  ret = log->Append(Slice(input), &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, 0);

  ASSERT_TRUE(Slice(input) == Slice(entry));

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

TEST_F(LibZLogTest, Trim) {
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
  ret = log->Append(Slice(), &pos);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  // can trim trimmed spot
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
}
