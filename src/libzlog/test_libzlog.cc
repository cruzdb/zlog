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
  std::cout << "OpenClose" << std::endl; 
  if (backend() != "lmdb") {
    std::cout << "OpenClose test not enabled for "
      << backend() << " backend" << std::endl;
    return;
  }

  const std::string input = "oh the input";

  uint64_t pos;
  int ret = log->Append(zlog::Slice(input), &pos);
  ASSERT_EQ(ret, 0);

  // destroy log client and reopen
  ret = reopen();
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

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
  uint64_t tail;
  int ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 100; i++) {
    uint64_t pos;
    ret = log->Append(zlog::Slice(), &pos);
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

#ifdef STREAMING_SUPPORT
TEST_P(LibZLogTest, Stream_MultiAppend) {
  {
    // empty set of streams
    std::set<uint64_t> stream_ids;
    int ret = log->MultiAppend(zlog::Slice(), stream_ids, NULL);
    ASSERT_EQ(ret, -EINVAL);
  }

  std::deque<std::set<uint64_t>> stream_ids_list;
  std::vector<uint64_t> pos_list;

  /*
   * Generate a bunch of random sets of stream ids and do an append. Save the
   * position and set for each case.
   */
  for (int i = 0; i < 100; i++) {
    std::vector<unsigned int> indicies(10);
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    int count = rand() % 9 + 1;
    for (int j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    uint64_t pos;
    int ret = log->MultiAppend(zlog::Slice(), stream_ids, &pos);
    ASSERT_EQ(ret, 0);

    stream_ids_list.push_back(stream_ids);
    pos_list.push_back(pos);
  }

  // compare log entries to saved stream sets from above
  for (unsigned i = 0; i < pos_list.size(); i++) {
    uint64_t pos = pos_list[i];

    std::set<uint64_t> stream_ids_out;
    int ret = log->StreamMembership(stream_ids_out, pos);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_ids_out, stream_ids_list[i]);
  }
}

TEST_P(LibZLogTest, Stream_StreamId) {
  zlog::Stream *stream0;
  int ret = log->OpenStream(0, &stream0);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream0->Id(), (uint64_t)0);

  delete stream0;

  zlog::Stream *stream33;
  ret = log->OpenStream(33, &stream33);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream33->Id(), (uint64_t)33);

  delete stream33;
}

TEST_P(LibZLogTest, Stream_Append) {
  zlog::Stream *stream;
  int ret = log->OpenStream(0, &stream);
  ASSERT_EQ(ret, 0);

  // nothing in stream
  uint64_t pos = 99;
  std::string entry;
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // add something to stream
  uint64_t pos2;
  ret = stream->Append(zlog::Slice(entry), &pos2);
  ASSERT_EQ(ret, 0);

  // still don't see it...
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // update view
  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);

  delete stream;
}

TEST_P(LibZLogTest, Stream_ReadNext) {
  zlog::Stream *stream;
  int ret = log->OpenStream(0, &stream);
  ASSERT_EQ(ret, 0);

  // empty
  uint64_t pos = 99;
  std::string entry;
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // still empty
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  char data[1234];

  // append something to the stream
  uint64_t pos2;
  ret = stream->Append(zlog::Slice(data, sizeof(data)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  std::string entry2;
  ret = stream->ReadNext(&entry2, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(zlog::Slice(data, sizeof(data)) == entry2);

  // we just read it, so it should be empty stream again
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  char data2[234];

  // again
  ret = stream->Append(zlog::Slice(data2, sizeof(data2)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(entry == zlog::Slice(data2, sizeof(data2)));

  // we just read it, so it should be empty stream again
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  delete stream;
}

TEST_P(LibZLogTest, Stream_Reset) {
  zlog::Stream *stream;
  int ret = log->OpenStream(0, &stream);
  ASSERT_EQ(ret, 0);

  // empty
  uint64_t pos = 99;
  std::string entry;
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  ret = stream->Reset();
  ASSERT_EQ(ret, 0);

  // still empty
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // append something to the stream
  char data[1234];

  uint64_t pos2;
  ret = stream->Append(zlog::Slice(data, sizeof(data)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(zlog::Slice(entry) == zlog::Slice(data, sizeof(data)));

  // we just read it, so it should be empty stream again
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  // go back to beginning
  ret = stream->Reset();
  ASSERT_EQ(ret, 0);

  // we see the same thing again
  std::string entry2;
  ret = stream->ReadNext(&entry2, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(entry == entry2);

  delete stream;
}

TEST_P(LibZLogTest, Stream_Sync) {
  // initialize some streams (note stream id = position)
  std::vector<zlog::Stream*> streams(10);
  for (unsigned i = 0; i < 10; i++) {
    int ret = log->OpenStream(i, &streams[i]);
    ASSERT_EQ(ret, 0);
  }

  // an empty stream sync is OK
  ASSERT_TRUE(streams[4]->History().empty());
  int ret = streams[4]->Sync();
  ASSERT_EQ(ret, 0);

  std::vector<std::vector<uint64_t>> stream_history(streams.size());

  /*
   * Do a bunch of random stream appends
   */
  for (unsigned i = 0; i < 100; i++) {
    // this assumes that the stream ids are 0..streams.size() change this to
    // adapt to another stream naming scheme.
    std::vector<unsigned int> indicies(streams.size());
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    unsigned count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    uint64_t pos;
    ret = log->MultiAppend(zlog::Slice(), stream_ids, &pos);
    ASSERT_EQ(ret, 0);

    for (std::set<uint64_t>::iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_history[stream_id].push_back(pos);
    }
  }

  // perform a sync on each stream. this will exercise the sync command when
  // it is first populating the history. the stream history internally should
  // match our view of the history.
  for (unsigned i = 0; i < streams.size(); i++) {
    ret = streams[i]->Sync();
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_history[i], streams[i]->History());
  }

  /*
   * Now repeat the process and do the sync again to exercise the code where
   * the sync has been initialized and we are adding more elements.
   */
  for (unsigned i = 0; i < 100; i++) {
    // this assumes that the stream ids are 0..streams.size() change this to
    // adapt to another stream naming scheme.
    std::vector<unsigned int> indicies(streams.size());
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    unsigned count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    uint64_t pos;
    ret = log->MultiAppend(zlog::Slice(), stream_ids, &pos);
    ASSERT_EQ(ret, 0);

    for (std::set<uint64_t>::iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_history[stream_id].push_back(pos);
    }
  }

  // re-verify
  for (unsigned i = 0; i < streams.size(); i++) {
    ret = streams[i]->Sync();
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_history[i], streams[i]->History());
  }

  for (unsigned i = 0; i < 10; i++) {
    delete streams[i];
  }
}
#endif

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

#ifdef STREAMING_SUPPORT
TEST_P(LibZLogCAPITest, Stream_MultiAppend) {
  // empty set of streams
  int ret = zlog_multiappend(log, NULL, 1, NULL, 0, NULL);
  ASSERT_EQ(ret, -EINVAL);

  std::deque<std::set<uint64_t>> stream_ids_list;
  std::vector<uint64_t> pos_list;

  /*
   * Generate a bunch of random sets of stream ids and do an append. Save the
   * position and set for each case.
   */
  for (int i = 0; i < 100; i++) {
    std::vector<unsigned int> indicies(10);
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    int count = rand() % 9 + 1;
    for (int j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    char data[1];
    std::vector<uint64_t> stream_ids_vec;
    for (auto it = stream_ids.begin(); it != stream_ids.end(); it++)
      stream_ids_vec.push_back(*it);

    uint64_t pos;
    ret = zlog_multiappend(log, data, sizeof(data),
        &stream_ids_vec[0], stream_ids_vec.size(), &pos);
    ASSERT_EQ(ret, 0);

    stream_ids_list.push_back(stream_ids);
    pos_list.push_back(pos);
  }

  // compare log entries to saved stream sets from above
  for (unsigned i = 0; i < pos_list.size(); i++) {
    uint64_t pos = pos_list[i];

    std::vector<uint64_t> stream_ids_out_vec;
    stream_ids_out_vec.resize(100);

    ret = zlog_stream_membership(log,
        &stream_ids_out_vec[0], 100, pos);
    ASSERT_GE(ret, 0);

    std::set<uint64_t> stream_ids_out;
    for (int i = 0; i < ret; i++)
      stream_ids_out.insert(stream_ids_out_vec[i]);

    ASSERT_EQ(stream_ids_out, stream_ids_list[i]);
  }
}

TEST_P(LibZLogCAPITest, Stream_ReadNext) {
  zlog_stream_t stream;
  int ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  char data[2048];

  // empty
  uint64_t pos = 99;
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // still empty
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  char data2[1234];

  // append something to the stream
  uint64_t pos2;
  ret = zlog_stream_append(stream, data2, sizeof(data2), &pos2);
  ASSERT_EQ(ret, 0);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ((unsigned)ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);

  // we just read it, so it should be empty stream again
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  char data3[234];

  // again
  ret = zlog_stream_append(stream, data3, sizeof(data3), &pos2);
  ASSERT_EQ(ret, 0);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  char data4[2340];

  // we should see it now..
  ret = zlog_stream_readnext(stream, data4, sizeof(data4), &pos);
  ASSERT_EQ((unsigned)ret, sizeof(data3));
  ASSERT_EQ(pos, pos2);

  // we just read it, so it should be empty stream again
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);
}

TEST_P(LibZLogCAPITest, Stream_Reset) {
  zlog_stream_t stream;
  int ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  char data[1];

  // empty
  uint64_t pos = 99;
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  ret = zlog_stream_reset(stream);
  ASSERT_EQ(ret, 0);

  // still empty
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // append something to the stream
  char data2[1234];

  uint64_t pos2;
  ret = zlog_stream_append(stream, data2, sizeof(data2), &pos2);
  ASSERT_EQ(ret, 0);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  char data3[2345];

  // we should see it now..
  ret = zlog_stream_readnext(stream, data3, sizeof(data3), &pos);
  ASSERT_EQ((unsigned)ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);

  // we just read it, so it should be empty stream again
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  // go back to beginning
  ret = zlog_stream_reset(stream);
  ASSERT_EQ(ret, 0);

  // we see the same thing again
  ret = zlog_stream_readnext(stream, data3, sizeof(data3), &pos);
  ASSERT_EQ((unsigned)ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);
}

TEST_P(LibZLogCAPITest, Stream_Sync) {
  // initialize some streams (note stream id = position)
  std::vector<zlog_stream_t> streams(10);
  for (unsigned i = 0; i < 10; i++) {
    int ret = zlog_stream_open(log, i, &streams[i]);
    ASSERT_EQ(ret, 0);
  }

  // an empty stream sync is OK
  ASSERT_EQ(zlog_stream_history(streams[4], NULL, 0), (unsigned)0);
  int ret = zlog_stream_sync(streams[4]);
  ASSERT_EQ(ret, 0);

  std::vector<std::vector<uint64_t>> stream_history(streams.size());

  /*
   * Do a bunch of random stream appends
   */
  for (unsigned i = 0; i < 100; i++) {
    // this assumes that the stream ids are 0..streams.size() change this to
    // adapt to another stream naming scheme.
    std::vector<unsigned int> indicies(streams.size());
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    unsigned count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    char data[1];
    std::vector<uint64_t> stream_ids_vec;
    for (auto it = stream_ids.begin(); it != stream_ids.end(); it++)
      stream_ids_vec.push_back(*it);

    uint64_t pos;
    ret = zlog_multiappend(log, data, sizeof(data), &stream_ids_vec[0], stream_ids_vec.size(), &pos);
    ASSERT_EQ(ret, 0);

    for (std::set<uint64_t>::iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_history[stream_id].push_back(pos);
    }
  }

  // perform a sync on each stream. this will exercise the sync command when
  // it is first populating the history. the stream history internally should
  // match our view of the history.
  for (unsigned i = 0; i < streams.size(); i++) {
    ret = zlog_stream_sync(streams[i]);
    ASSERT_EQ(ret, 0);
    size_t history_size = zlog_stream_history(streams[i], NULL, 0);
    std::vector<uint64_t> h(history_size);
    ret = zlog_stream_history(streams[i], &h[0], history_size);
    ASSERT_EQ((unsigned)ret, history_size);
    ASSERT_EQ(stream_history[i], h);
  }

  /*
   * Now repeat the process and do the sync again to exercise the code where
   * the sync has been initialized and we are adding more elements.
   */
  for (unsigned i = 0; i < 100; i++) {
    // this assumes that the stream ids are 0..streams.size() change this to
    // adapt to another stream naming scheme.
    std::vector<unsigned int> indicies(streams.size());
    std::iota(indicies.begin(), indicies.end(), 0);
    std::random_shuffle(indicies.begin(), indicies.end());

    std::set<uint64_t> stream_ids;
    unsigned count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    char data[1];
    std::vector<uint64_t> stream_ids_vec;
    for (auto it = stream_ids.begin(); it != stream_ids.end(); it++)
      stream_ids_vec.push_back(*it);

    uint64_t pos;
    ret = zlog_multiappend(log, data, sizeof(data), &stream_ids_vec[0], stream_ids_vec.size(), &pos);
    ASSERT_EQ(ret, 0);

    for (std::set<uint64_t>::iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_history[stream_id].push_back(pos);
    }
  }

  // re-verify
  for (unsigned i = 0; i < streams.size(); i++) {
    ret = zlog_stream_sync(streams[i]);
    ASSERT_EQ(ret, 0);
    size_t history_size = zlog_stream_history(streams[i], NULL, 0);
    std::vector<uint64_t> h(history_size);
    ret = zlog_stream_history(streams[i], &h[0], history_size);
    ASSERT_EQ((unsigned)ret, history_size);
    ASSERT_EQ(stream_history[i], h);
  }
}

TEST_P(LibZLogCAPITest, Stream_StreamId) {
  zlog_stream_t stream0;
  int ret = zlog_stream_open(log, 0, &stream0);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(zlog_stream_id(stream0), (unsigned)0);

  zlog_stream_t stream33;
  ret = zlog_stream_open(log, 33, &stream33);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(zlog_stream_id(stream33), (unsigned)33);
}

TEST_P(LibZLogCAPITest, Stream_Append) {
  zlog_stream_t stream;
  int ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  // nothing in stream
  uint64_t pos = 99;
  ret = zlog_stream_readnext(stream, NULL, 0, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // add something to stream
  char data[5];
  uint64_t pos2;
  ret = zlog_stream_append(stream, data, sizeof(data), &pos2);
  ASSERT_EQ(ret, 0);

  // still don't see it...
  ret = zlog_stream_readnext(stream, NULL, 0, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // update view
  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ((unsigned)ret, sizeof(data));
  ASSERT_EQ(pos, pos2);
}
#endif
