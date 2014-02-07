#include <errno.h>
#include <rados/librados.hpp>
#include <gtest/gtest.h>
#include "libzlog.h"

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

  zlog::Log *log;

  int ret = zlog::Log::Create(ioctx, "mylog", 0, &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Create(ioctx, "mylog", -1, &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Create(ioctx, "", 5, &log);
  ASSERT_EQ(ret, -EINVAL);

  ret = zlog::Log::Create(ioctx, "mylog", 5, &log);
  ASSERT_EQ(ret, 0);

  ret = zlog::Log::Create(ioctx, "mylog", 5, &log);
  ASSERT_EQ(ret, -EEXIST);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, rados));
}
