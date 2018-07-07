#include <iostream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "zlog/backend/ceph.h"
#include "port/stack_trace.h"

void BackendTest::SetUp() {}
void BackendTest::TearDown() {}

struct UniquePoolContext {
  rados_t cluster = nullptr;
  rados_ioctx_t ioctx = nullptr;
  std::string pool_name = "";

  void Init() {
    boost::uuids::uuid uuid = boost::uuids::random_generator()();
    std::string pool = "cls_zlog_test." + boost::uuids::to_string(uuid);

    int ret = rados_create(&cluster, NULL);
    ASSERT_EQ(ret, 0);

    ret = rados_conf_read_file(cluster, NULL);
    ASSERT_EQ(ret, 0);

    ret = rados_connect(cluster);
    ASSERT_EQ(ret, 0);

    ret = rados_pool_create(cluster, pool.c_str());
    ASSERT_EQ(ret, 0);

    pool_name = pool;

    ret = rados_ioctx_create(cluster, pool_name.c_str(), &ioctx);
    ASSERT_EQ(ret, 0);
  }

  virtual ~UniquePoolContext() {
    if (ioctx) {
      rados_ioctx_destroy(ioctx);
    }
    if (pool_name.size()) {
      rados_pool_delete(cluster, pool_name.c_str());
    }
    if (cluster) {
      rados_shutdown(cluster);
    }
  }
};

struct LibZLogTest::Context : public UniquePoolContext {
  librados::IoCtx ioctxpp;
  bool close_ioctxpp = false;

  void Init(bool lowlevel) {
    ASSERT_NO_FATAL_FAILURE(UniquePoolContext::Init());
    if (lowlevel) {
      librados::IoCtx::from_rados_ioctx_t(ioctx, ioctxpp);
      close_ioctxpp = true;
    }
  }

  ~Context() {
    if (close_ioctxpp) {
      ioctxpp.close();
    }
  }
};

void LibZLogTest::SetUp() {
  context = new Context;
  ASSERT_NO_FATAL_FAILURE(context->Init(lowlevel()));

  if (lowlevel()) {
    ASSERT_TRUE(exclusive());
    auto backend = std::unique_ptr<zlog::Backend>(
        new zlog::storage::ceph::CephBackend(&context->ioctxpp));
    int ret = zlog::Log::CreateWithBackend(options,
        std::move(backend), "mylog", &log);
    ASSERT_EQ(ret, 0);
  } else {
    std::string host = "";
    std::string port = "";
    if (exclusive()) {
    } else {
      host = "localhost";
      port = "5678";
    }
    int ret = zlog::Log::Create(options, "ceph", "mylog",
        {{"conf_file", ""}, {"pool", context->pool_name}},
        host, port, &log);
    ASSERT_EQ(ret, 0);
  }
}

void LibZLogTest::TearDown() {
  if (log)
    delete log;
  if (context)
    delete context;
}

int LibZLogTest::reopen()
{
  return -EOPNOTSUPP;
}

std::string LibZLogTest::backend()
{
  return "ceph";
}

struct LibZLogCAPITest::Context : public UniquePoolContext {
};

void LibZLogCAPITest::SetUp() {
  context = new Context;
  ASSERT_NO_FATAL_FAILURE(context->Init());

  ASSERT_FALSE(lowlevel());

  std::string host = "";
  std::string port = "";
  if (exclusive()) {
    host = "localhost";
    port = "5678";
  }

  const char *keys[] = {"conf_file", "pool"};
  const char *vals[] = {"", context->pool_name.c_str()};
  int ret = zlog_create(&options, "ceph", "c_mylog",
      keys, vals, 2, host.c_str(), port.c_str(), &log);
  ASSERT_EQ(ret, 0);
}

void LibZLogCAPITest::TearDown() {
  if (log)
    zlog_destroy(log);

  if (context)
    delete context;
}
INSTANTIATE_TEST_CASE_P(Level, LibZLogTest,
    ::testing::Values(
      std::make_tuple(true, true),
      std::make_tuple(false, true),
      std::make_tuple(false, false)));

INSTANTIATE_TEST_CASE_P(LevelCAPI, LibZLogCAPITest,
    ::testing::Values(
      std::make_tuple(false, true),
      std::make_tuple(false, false)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
