#include <gtest/gtest.h>
#include <rados/librados.hpp>
#include <rados/librados.h>
#include <deque>
#include "include/zlog/log.h"
#include "include/zlog/capi.h"
#include "include/zlog/ceph_backend.h"

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

class LibZlog : public ::testing::Test {
 public:
  void SetUp() {
    pool_name = get_temp_pool_name();
    ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
    ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));
    be = new CephBackend(&ioctx);
    client = new zlog::SeqrClient("localhost", "5678");
    ASSERT_NO_THROW(client->Connect());
  }

  void TearDown() {
    delete be;
    delete client;
    ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
  }

  Backend  *be;
  zlog::SeqrClient *client;


 private:
  librados::IoCtx ioctx;
  std::string pool_name;
  librados::Rados rados;
};

class LibZlogStream : public LibZlog {};

// common tests
#include "test.cc"

// below are tests that are so far not ported to generic backend
//
class LibZlogC : public ::testing::Test {
 public:
  void SetUp() {
    pool_name = get_temp_pool_name();
    ASSERT_EQ(0, create_one_pool_pp(pool_name, &rados));
    ASSERT_EQ(0, rados_ioctx_create(rados, pool_name.c_str(), &ioctx));
  }

  void TearDown() {
    ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
  }

  rados_ioctx_t ioctx;

 private:
  rados_t rados;
  std::string pool_name;
};

class LibZlogCStream : public LibZlogC {};

TEST_F(LibZlogC, Trim) {
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
}

TEST_F(LibZlogC, Create) {
  zlog_log_t log;

  int ret = zlog_create(ioctx, "", "localhost", "5678", &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, 0);

  ret = zlog_destroy(log);
  ASSERT_EQ(ret, 0);

  ret = zlog_create(ioctx, "mylog", "localhost", "5678", &log);
  ASSERT_EQ(ret, -EEXIST);
}

TEST_F(LibZlogC, Open) {
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
}

TEST_F(LibZlogC, CheckTail) {
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
}

TEST_F(LibZlogC, Append) {
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
}

TEST_F(LibZlogC, Fill) {
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
}

TEST_F(LibZlogC, Read) {
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
}

TEST_F(LibZlogCStream, MultiAppend) {
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
}

TEST_F(LibZlogCStream, ReadNext) {
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
}

TEST_F(LibZlogCStream, Reset) {
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
}

TEST_F(LibZlogCStream, Sync) {
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
}

TEST_F(LibZlogCStream, StreamId) {
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
}

TEST_F(LibZlogCStream, Append) {
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
}
