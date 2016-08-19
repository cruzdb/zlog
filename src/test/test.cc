/*
 * This file is dropped into test_xxx.cc where xxx is the backend being
 * tested. That test_xxx.cc file defines the fixture and results in a separate
 * executable. It would be nice avoid this using some gtest advanced features!
 */

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

TEST_F(LibZlog, Aio) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

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

TEST_F(LibZlog, Create) {
  zlog::Log *log = NULL;

  int ret = zlog::Log::Create(be, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  // TODO: creating a log with NULL seqclient should be an error
  ret = zlog::Log::Create(be, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::Log::Create(be, "mylog", NULL, &log);
  ASSERT_EQ(ret, -EEXIST);
  ASSERT_EQ(log, nullptr);
}

TEST_F(LibZlog, Open) {
  zlog::Log *log = NULL;

  int ret = zlog::Log::Open(be, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  ret = zlog::Log::Open(be, "dne", NULL, &log);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(log, nullptr);

  ret = zlog::Log::Create(be, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::Log::Open(be, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
}

TEST_F(LibZlog, CheckTail) {

  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  delete log;
}

TEST_F(LibZlog, Append) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
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

  delete log;
}

TEST_F(LibZlog, Fill) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(0);
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

  delete log;
}

TEST_F(LibZlog, Read) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  std::string entry;
  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -ENODEV);

  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Read(0, &entry);
  ASSERT_EQ(ret, -EFAULT);

  ret = log->Read(232, &entry);
  ASSERT_EQ(ret, -ENODEV);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Read(232, &entry);
  ASSERT_EQ(ret, -EFAULT);

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
  ASSERT_EQ(ret, -EFAULT);

  // same for unwritten position
  pos = 456;
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);
  ret = log->Read(pos, &entry);
  ASSERT_EQ(ret, -EFAULT);

  delete log;
}

TEST_F(LibZlog, Trim) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  // can trim empty spot
  ret = log->Trim(55);
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

  delete log;
}

TEST_F(LibZlogStream, MultiAppend) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  {
    // empty set of streams
    std::set<uint64_t> stream_ids;
    ret = log->MultiAppend(Slice(), stream_ids, NULL);
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
    ret = log->MultiAppend(Slice(), stream_ids, &pos);
    ASSERT_EQ(ret, 0);

    stream_ids_list.push_back(stream_ids);
    pos_list.push_back(pos);
  }

  // compare log entries to saved stream sets from above
  for (unsigned i = 0; i < pos_list.size(); i++) {
    uint64_t pos = pos_list[i];

    std::set<uint64_t> stream_ids_out;
    ret = log->StreamMembership(stream_ids_out, pos);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_ids_out, stream_ids_list[i]);
  }

  delete log;
}

TEST_F(LibZlogStream, StreamId) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  zlog::Stream *stream0;
  ret = log->OpenStream(0, &stream0);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream0->Id(), (uint64_t)0);

  delete stream0;

  zlog::Stream *stream33;
  ret = log->OpenStream(33, &stream33);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream33->Id(), (uint64_t)33);

  delete stream33;

  delete log;
}

TEST_F(LibZlogStream, Append) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  zlog::Stream *stream;
  ret = log->OpenStream(0, &stream);
  ASSERT_EQ(ret, 0);

  // nothing in stream
  uint64_t pos = 99;
  std::string entry;
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, (uint64_t)99);

  // add something to stream
  uint64_t pos2;
  ret = stream->Append(Slice(entry), &pos2);
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

  delete log;
}

TEST_F(LibZlogStream, ReadNext) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  zlog::Stream *stream;
  ret = log->OpenStream(0, &stream);
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
  ret = stream->Append(Slice(data, sizeof(data)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  std::string entry2;
  ret = stream->ReadNext(&entry2, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(Slice(data, sizeof(data)) == entry2);

  // we just read it, so it should be empty stream again
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  char data2[234];

  // again
  ret = stream->Append(Slice(data2, sizeof(data2)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(entry == Slice(data2, sizeof(data2)));

  // we just read it, so it should be empty stream again
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  delete stream;

  delete log;
}

TEST_F(LibZlogStream, Reset) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  zlog::Stream *stream;
  ret = log->OpenStream(0, &stream);
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
  ret = stream->Append(Slice(data, sizeof(data)), &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream->Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream->ReadNext(&entry, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_TRUE(Slice(entry) == Slice(data, sizeof(data)));

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

  delete log;
}

TEST_F(LibZlogStream, Sync) {
  zlog::Log *log;
  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);

  // initialize some streams (note stream id = position)
  std::vector<zlog::Stream*> streams(10);
  for (unsigned i = 0; i < 10; i++) {
    ret = log->OpenStream(i, &streams[i]);
    ASSERT_EQ(ret, 0);
  }

  // an empty stream sync is OK
  ASSERT_TRUE(streams[4]->History().empty());
  ret = streams[4]->Sync();
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
    ret = log->MultiAppend(Slice(), stream_ids, &pos);
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
    ret = log->MultiAppend(Slice(), stream_ids, &pos);
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

  delete log;
}

