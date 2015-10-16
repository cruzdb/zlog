#include <errno.h>
#include <rados/librados.hpp>
#include <gtest/gtest.h>
#include "libzlog.hpp"

/*
 * Helper function from ceph/src/test/librados/test.cc
 */
std::string get_temp_pool_name()
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

/*
 * Helper function from ceph/src/test/librados/test.cc
 */
std::string create_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
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
int destroy_one_pool_pp(const std::string &pool_name, librados::Rados &cluster)
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

  zlog::Log log;

  int ret = zlog::Log::Create(ioctx, "mylog", 0, NULL, log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Create(ioctx, "mylog", -1, NULL, log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Create(ioctx, "", 5, NULL, log);
  ASSERT_EQ(ret, -EINVAL);

  // TODO: creating a log with NULL seqclient should be an error
  ret = zlog::Log::Create(ioctx, "mylog", 5, NULL, log);
  ASSERT_EQ(ret, 0);

  ret = zlog::Log::Create(ioctx, "mylog", 5, NULL, log);
  ASSERT_EQ(ret, -EEXIST);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlog, Open) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::Log log;

  int ret = zlog::Log::Open(ioctx, "", NULL, log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Open(ioctx, "dne", NULL, log);
  ASSERT_EQ(ret, -ENOENT);

  ret = zlog::Log::Create(ioctx, "mylog", 5, NULL, log);
  ASSERT_EQ(ret, 0);
  ret = zlog::Log::Open(ioctx, "mylog", NULL, log);
  ASSERT_EQ(ret, 0);

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

  zlog::Log log;
  int ret = zlog::Log::Create(ioctx, "mylog", 5, &client, log);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log.CheckTail(&pos, false);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log.CheckTail(&pos, false);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  ret = log.CheckTail(&pos, true);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)1);

  ret = log.CheckTail(&pos, true);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)2);

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

  zlog::Log log;
  int ret = zlog::Log::Create(ioctx, "mylog", 5, &client, log);
  ASSERT_EQ(ret, 0);

  uint64_t last = 0;
  for (int i = 0; i < 100; i++) {
    uint64_t pos;
    ceph::bufferlist bl;
    ret = log.Append(bl, &pos);
    ASSERT_EQ(ret, 0);

    ASSERT_GT(pos, last);
    last = pos;

    uint64_t tail;
    ret = log.CheckTail(&tail, false);
    ASSERT_EQ(ret, 0);
    ASSERT_EQ(pos, tail);
  }

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

  zlog::Log log;
  int ret = zlog::Log::Create(ioctx, "mylog", 5, &client, log);
  ASSERT_EQ(ret, 0);

  ret = log.Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log.Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log.Fill(232);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ceph::bufferlist bl;
  ret = log.Append(bl, &pos);
  ASSERT_EQ(ret, 0);

  ret = log.Fill(pos);
  ASSERT_EQ(ret, -EROFS);

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

  zlog::Log log;
  int ret = zlog::Log::Create(ioctx, "mylog", 5, &client, log);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = log.Read(0, bl);
  ASSERT_EQ(ret, -ENODEV);

  ret = log.Fill(0);
  ASSERT_EQ(ret, 0);

  ret = log.Read(0, bl);
  ASSERT_EQ(ret, -EFAULT);

  ret = log.Read(232, bl);
  ASSERT_EQ(ret, -ENODEV);

  ret = log.Fill(232);
  ASSERT_EQ(ret, 0);

  ret = log.Read(232, bl);
  ASSERT_EQ(ret, -EFAULT);

  uint64_t pos;
  bl.append("asdfasdfasdf");
  ret = log.Append(bl, &pos);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl2;
  ret = log.Read(pos, bl2);
  ASSERT_EQ(ret, 0);

  ASSERT_TRUE(bl == bl2);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}
