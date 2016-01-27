#include <cerrno>
#include <deque>
#include <rados/librados.hpp>
#include <rados/librados.h>
#include <gtest/gtest.h>
#include "libzlog.hpp"
#include "libzlog.h"

/*
 * Helper function from ceph/src/test/librados/test.cc
 */
static std::string get_temp_pool_name()
{
  char hostname[80];
  char out[80];
  memset(hostname, 0, sizeof(hostname));
  memset(out, 0, sizeof(out));
  gethostname(hostname, sizeof(hostname)-1);
  static int num = 1;
  sprintf(out, "%s-%d-%d", hostname, getpid(), num);
  num++;
  std::string prefix("test-rados-api-");
  prefix += out;
  return prefix;
}

static int create_one_pool_pp(const std::string &pool_name, rados_t *rados)
{
  int ret = rados_create(rados, NULL);
  if (ret)
    return ret;
  ret = rados_conf_read_file(*rados, NULL);
  if (ret)
    return ret;
  ret = rados_conf_parse_env(*rados, NULL);
  if (ret)
    return ret;
  ret = rados_connect(*rados);
  if (ret)
    return ret;
  ret = rados_pool_create(*rados, pool_name.c_str());
  if (ret)
    return ret;
  return 0;
}

static int destroy_one_pool_pp(const std::string &pool_name, rados_t rados)
{
  int ret = rados_pool_delete(rados, pool_name.c_str());
  if (ret) {
    rados_shutdown(rados);
    return ret;
  }
  rados_shutdown(rados);
  return 0;
}

/*
 * Helper function from ceph/src/test/librados/test.cc
 */
static std::string create_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
{
  char *id = getenv("CEPH_CLIENT_ID");
  if (id) std::cerr << "Client id is: " << id << std::endl;

  int ret;
  ret = cluster.init(id);
  if (ret) {
    std::ostringstream oss;
    oss << "cluster.init failed with error " << ret;
    return oss.str();
  }
  ret = cluster.conf_read_file(NULL);
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.conf_read_file failed with error " << ret;
    return oss.str();
  }
  cluster.conf_parse_env(NULL);
  ret = cluster.connect();
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.connect failed with error " << ret;
    return oss.str();
  }
  ret = cluster.pool_create(pool_name.c_str());
  if (ret) {
    cluster.shutdown();
    std::ostringstream oss;
    oss << "cluster.pool_create(" << pool_name << ") failed with error " << ret;
    return oss.str();
  }
  return "";
}

/*
 * Helper function from ceph/src/test/librados/test.cc
 */
static int destroy_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
{
  int ret = cluster.pool_delete(pool_name.c_str());
  if (ret) {
    cluster.shutdown();
    return ret;
  }
  cluster.shutdown();
  return 0;
}

TEST(LibZlog, Create) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::LogHL *log = NULL;

  int ret = zlog::LogHL::Create(ioctx, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  // TODO: creating a log with NULL seqclient should be an error
  ret = zlog::LogHL::Create(ioctx, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::LogHL::Create(ioctx, "mylog", NULL, &log);
  ASSERT_EQ(ret, -EEXIST);
  ASSERT_EQ(log, nullptr);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Open) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::LogHL *log = NULL;

  int ret = zlog::LogHL::Open(ioctx, "", NULL, &log);
  ASSERT_EQ(ret, -EINVAL);
  ASSERT_EQ(log, nullptr);

  ret = zlog::LogHL::Open(ioctx, "dne", NULL, &log);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(log, nullptr);

  ret = zlog::LogHL::Create(ioctx, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;
  log = NULL;

  ret = zlog::LogHL::Open(ioctx, "mylog", NULL, &log);
  ASSERT_EQ(ret, 0);
  ASSERT_NE(log, nullptr);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, CheckTail) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log->CheckTail(&pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Append) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = log->CheckTail(&tail);
  ASSERT_EQ(ret, 0);

  for (int i = 0; i < 100; i++) {
    uint64_t pos;
    ceph::bufferlist bl;
    ret = log->Append(bl, &pos);
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

  ceph::bufferlist bl;
  ret = log->Append(bl, &pos2);
  ASSERT_EQ(ret, 0);
  ASSERT_GT(pos2, pos);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, MultiAppend) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;

  {
    // empty set of streams
    std::set<uint64_t> stream_ids;
    ret = log->MultiAppend(bl, stream_ids, NULL);
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
    ret = log->MultiAppend(bl, stream_ids, &pos);
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

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, StreamId) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  zlog::LogHL::Stream stream0;
  ret = log->OpenStream(0, stream0);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream0.Id(), 0);

  zlog::LogHL::Stream stream33;
  ret = log->OpenStream(33, stream33);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(stream33.Id(), 33);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, Append) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  zlog::LogHL::Stream stream;
  ret = log->OpenStream(0, stream);
  ASSERT_EQ(ret, 0);

  // nothing in stream
  uint64_t pos = 99;
  ceph::bufferlist bl;
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  // add something to stream
  uint64_t pos2;
  ret = stream.Append(bl, &pos2);
  ASSERT_EQ(ret, 0);

  // still don't see it...
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  // update view
  ret = stream.Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, ReadNext) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  zlog::LogHL::Stream stream;
  ret = log->OpenStream(0, stream);
  ASSERT_EQ(ret, 0);

  // empty
  uint64_t pos = 99;
  ceph::bufferlist bl;
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  ret = stream.Sync();
  ASSERT_EQ(ret, 0);

  // still empty
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  char data[1234];

  // append something to the stream
  uint64_t pos2;
  bl.clear();
  bl.append(data, sizeof(data));
  ret = stream.Append(bl, &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream.Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ceph::bufferlist bl_out;
  ret = stream.ReadNext(bl_out, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_EQ(bl, bl_out);

  // we just read it, so it should be empty stream again
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  char data2[234];

  // again
  bl.clear();
  bl.append(data2, sizeof(data2));
  ret = stream.Append(bl, &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream.Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  bl_out.clear();
  ret = stream.ReadNext(bl_out, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_EQ(bl, bl_out);

  // we just read it, so it should be empty stream again
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, Reset) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  zlog::LogHL::Stream stream;
  ret = log->OpenStream(0, stream);
  ASSERT_EQ(ret, 0);

  // empty
  uint64_t pos = 99;
  ceph::bufferlist bl;
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  ret = stream.Reset();
  ASSERT_EQ(ret, 0);

  // still empty
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  // append something to the stream
  char data[1234];

  uint64_t pos2;
  bl.clear();
  bl.append(data, sizeof(data));
  ret = stream.Append(bl, &pos2);
  ASSERT_EQ(ret, 0);

  ret = stream.Sync();
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ceph::bufferlist bl_out;
  ret = stream.ReadNext(bl_out, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_EQ(bl, bl_out);

  // we just read it, so it should be empty stream again
  ret = stream.ReadNext(bl, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  // go back to beginning
  ret = stream.Reset();
  ASSERT_EQ(ret, 0);

  // we see the same thing again
  bl_out.clear();
  ret = stream.ReadNext(bl_out, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, pos2);
  ASSERT_EQ(bl, bl_out);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogStream, Sync) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  // initialize some streams (note stream id = position)
  std::vector<zlog::LogHL::Stream> streams(10);
  for (unsigned i = 0; i < 10; i++) {
    ret = log->OpenStream(i, streams[i]);
    ASSERT_EQ(ret, 0);
  }

  // an empty stream sync is OK
  ASSERT_TRUE(streams[4].History().empty());
  ret = streams[4].Sync();
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
    int count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    uint64_t pos;
    ceph::bufferlist bl;
    ret = log->MultiAppend(bl, stream_ids, &pos);
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
    ret = streams[i].Sync();
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_history[i], streams[i].History());
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
    int count = rand() % 9 + 1;
    for (unsigned j = 0; j < count; j++)
      stream_ids.insert(indicies[j]);

    uint64_t pos;
    ceph::bufferlist bl;
    ret = log->MultiAppend(bl, stream_ids, &pos);
    ASSERT_EQ(ret, 0);

    for (std::set<uint64_t>::iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      stream_history[stream_id].push_back(pos);
    }
  }

  // re-verify
  for (unsigned i = 0; i < streams.size(); i++) {
    ret = streams[i].Sync();
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(stream_history[i], streams[i].History());
  }

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Fill) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ceph::bufferlist bl;
  ret = log->Append(bl, &pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, -EROFS);

  // ok to fill a trimmed position
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  ret = log->Fill(pos);
  ASSERT_EQ(ret, 0);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Read) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = log->Read(0, bl);
  ASSERT_EQ(ret, -ENODEV);

  ret = log->Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log->Read(0, bl);
  ASSERT_EQ(ret, -EFAULT);

  ret = log->Read(232, bl);
  ASSERT_EQ(ret, -ENODEV);

  ret = log->Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log->Read(232, bl);
  ASSERT_EQ(ret, -EFAULT);

  uint64_t pos;
  bl.append("asdfasdfasdf");
  ret = log->Append(bl, &pos);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl2;
  ret = log->Read(pos, bl2);
  ASSERT_EQ(ret, 0);

  ASSERT_TRUE(bl == bl2);

  // trim a written position
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);
  ret = log->Read(pos, bl);
  ASSERT_EQ(ret, -EFAULT);

  // same for unwritten position
  pos = 456;
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);
  ret = log->Read(pos, bl);
  ASSERT_EQ(ret, -EFAULT);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Trim) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogHL *log;
  int ret = zlog::LogHL::Create(ioctx, "mylog", &client, &log);
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
  ceph::bufferlist bl;
  ret = log->Append(bl, &pos);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(pos);
  ASSERT_EQ(ret, 0);

  // can trim trimmed spot
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);
  ret = log->Trim(70);
  ASSERT_EQ(ret, 0);

  delete log;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Trim) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  // can trim empty spot
  ret = zlog_trim(log, 55);
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

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Create) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;

  int ret = zlog_create(ioctx, "", "localhost", "5678", &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, -EEXIST);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Open) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;

  int ret = zlog_open(ioctx, "", "localhost", "5678", &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog_open(ioctx, "dne", "localhost", "5678", &log);
  ASSERT_EQ(ret, -ENOENT);

  ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);
  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ret = zlog_open(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);
  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, CheckTail) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = zlog_checktail(log, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = zlog_checktail(log, &pos);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Append) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;

  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  uint64_t tail;
  ret = zlog_checktail(log, &tail);
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

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Fill) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;

  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  ret = zlog_fill(log, 0);
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

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogC, Read) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  char data[4096];

  ret = zlog_read(log, 0, data, sizeof(data));
  ASSERT_EQ(ret, -ENODEV);

  ret = zlog_fill(log, 0);
  ASSERT_EQ(ret, 0);

  ret = zlog_read(log, 0, data, sizeof(data));
  ASSERT_EQ(ret, -EFAULT);

  ret = zlog_read(log, 232, data, sizeof(data));
  ASSERT_EQ(ret, -ENODEV);

  ret = zlog_fill(log, 232);
  ASSERT_EQ(ret, 0);

  ret = zlog_read(log, 232, data, sizeof(data));
  ASSERT_EQ(ret, -EFAULT);

  const char *s = "asdfasdfasdfasdfasdfasdf";

  uint64_t pos;
  memset(data, 0, sizeof(data));
  sprintf(data, "%s", s);
  ret = zlog_append(log, data, sizeof(data), &pos);
  ASSERT_EQ(ret, 0);

  char data2[4096];
  memset(data2, 0, sizeof(data2));
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ(ret, sizeof(data2));

  ASSERT_TRUE(strcmp(data2, s) == 0);

  // trim a written position
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ(ret, -EFAULT);

  // same for unwritten position
  pos = 456;
  ret = zlog_trim(log, pos);
  ASSERT_EQ(ret, 0);
  ret = zlog_read(log, pos, data2, sizeof(data2));
  ASSERT_EQ(ret, -EFAULT);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, MultiAppend) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  // empty set of streams
  ret = zlog_multiappend(log, NULL, 1, NULL, 0, NULL);
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

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, ReadNext) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  zlog_stream_t stream;
  ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  char data[2048];

  // empty
  uint64_t pos = 99;
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // still empty
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  char data2[1234];

  // append something to the stream
  uint64_t pos2;
  ret = zlog_stream_append(stream, data2, sizeof(data2), &pos2);
  ASSERT_EQ(ret, 0);

  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);
  //ASSERT_EQ(bl, bl_out);

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
  ASSERT_EQ(ret, sizeof(data3));
  ASSERT_EQ(pos, pos2);
  //ASSERT_EQ(bl, bl_out);

  // we just read it, so it should be empty stream again
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, Reset) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  zlog_stream_t stream;
  ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  char data[1];

  // empty
  uint64_t pos = 99;
  ceph::bufferlist bl;
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  ret = zlog_stream_reset(stream);
  ASSERT_EQ(ret, 0);

  // still empty
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

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
  ASSERT_EQ(ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);
  //ASSERT_EQ(bl, bl_out); FIXME

  // we just read it, so it should be empty stream again
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, pos2);

  // go back to beginning
  ret = zlog_stream_reset(stream);
  ASSERT_EQ(ret, 0);

  // we see the same thing again
  ret = zlog_stream_readnext(stream, data3, sizeof(data3), &pos);
  ASSERT_EQ(ret, sizeof(data2));
  ASSERT_EQ(pos, pos2);
  //ASSERT_EQ(bl, bl_out);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, Sync) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  // initialize some streams (note stream id = position)
  std::vector<zlog_stream_t> streams(10);
  for (unsigned i = 0; i < 10; i++) {
    ret = zlog_stream_open(log, i, &streams[i]);
    ASSERT_EQ(ret, 0);
  }

  // an empty stream sync is OK
  ASSERT_EQ(zlog_stream_history(streams[4], NULL, 0), 0);
  ret = zlog_stream_sync(streams[4]);
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
    int count = rand() % 9 + 1;
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
    ASSERT_EQ(ret, history_size);
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
    int count = rand() % 9 + 1;
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
    ASSERT_EQ(ret, history_size);
    ASSERT_EQ(stream_history[i], h);
  }

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, StreamId) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  zlog_stream_t stream0;
  ret = zlog_stream_open(log, 0, &stream0);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(zlog_stream_id(stream0), 0);

  zlog_stream_t stream33;
  ret = zlog_stream_open(log, 33, &stream33);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(zlog_stream_id(stream33), 33);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogCStream, Append) {
  rados_t rados;
  rados_ioctx_t ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
  ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));

  zlog_log_t log;
  int ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  zlog_stream_t stream;
  ret = zlog_stream_open(log, 0, &stream);
  ASSERT_EQ(ret, 0);

  // nothing in stream
  uint64_t pos = 99;
  ret = zlog_stream_readnext(stream, NULL, 0, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  // add something to stream
  char data[5];
  uint64_t pos2;
  ret = zlog_stream_append(stream, data, sizeof(data), &pos2);
  ASSERT_EQ(ret, 0);

  // still don't see it...
  ret = zlog_stream_readnext(stream, NULL, 0, &pos);
  ASSERT_EQ(ret, -EBADF);
  ASSERT_EQ(pos, 99);

  // update view
  ret = zlog_stream_sync(stream);
  ASSERT_EQ(ret, 0);

  // we should see it now..
  ret = zlog_stream_readnext(stream, data, sizeof(data), &pos);
  ASSERT_EQ(ret, sizeof(data));
  ASSERT_EQ(pos, pos2);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}
