#include <cerrno>
#include <deque>
#include <rados/librados.hpp>
#include <rados/librados.h>
#include <gtest/gtest.h>
#include "libzlog/libzlog.hpp"
#include "libzlog/libzlog.h"
#include "libzlog/internal.hpp"

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

TEST(LibZlogInternal, CheckTailBatch) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogImpl log;
  int ret = zlog::LogImpl::Create(ioctx, "mylog", 5, &client, log);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  ret = log.CheckTail(&pos, false);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)0);

  std::vector<uint64_t> result;
  ret = log.CheckTail(result, 1);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(result[0], 0);

  ret = log.CheckTail(result, 5);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(result[0], 1);
  ASSERT_EQ(result[1], 2);
  ASSERT_EQ(result[2], 3);
  ASSERT_EQ(result[3], 4);
  ASSERT_EQ(result[4], 5);

  ret = log.CheckTail(&pos, false);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)6);

  ret = log.CheckTail(&pos, true);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)6);

  ret = log.CheckTail(result, 2);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(result[0], 7);
  ASSERT_EQ(result[1], 8);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}

TEST(LibZlogInternal, CheckTail) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, rados));
  ASSERT_EQ(0, rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::LogImpl log;
  int ret = zlog::LogImpl::Create(ioctx, "mylog", 5, &client, log);
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
  ASSERT_EQ(pos, (unsigned)0);

  ret = log.CheckTail(&pos, true);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(pos, (unsigned)1);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}
