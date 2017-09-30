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

// 4.1 use scheme in seqr
// 4. make sure linking is all awesome
// 5. figure out what to do with create/open tests
//   - non fixture based test?
// CreateWithBackend
// (3): shared, exclusive
// remove pool
// apple dynlib

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
  CephBackend *backend = nullptr;
  zlog::SeqrClient *client = nullptr;

  void Init(bool lowlevel) {
    ASSERT_NO_FATAL_FAILURE(UniquePoolContext::Init());
    if (lowlevel) {
      librados::IoCtx::from_rados_ioctx_t(ioctx, ioctxpp);
      close_ioctxpp = true;
    }
  }

  ~Context() {
    if (client) {
      delete client;
    }
    if (backend) {
      delete backend;
    }
    if (close_ioctxpp) {
      ioctxpp.close();
    }
  }
};

void LibZLogTest::SetUp() {
  context = new Context;
  ASSERT_NO_FATAL_FAILURE(context->Init(lowlevel()));

  if (exclusive()) {
    // default is ok
  } else {
    context->client = new zlog::SeqrClient("localhost", "5678");
    ASSERT_NO_THROW(context->client->Connect());
  }

  if (lowlevel()) {
    context->backend = new CephBackend(&context->ioctxpp);
    int ret = zlog::Log::Create(context->backend, "mylog",
        context->client, &log);
    ASSERT_EQ(ret, 0);
  } else {
    int ret = zlog::Log::Create("ceph", "mylog",
        {{"conf_file", ""}, {"pool", context->pool_name}},
        context->client, &log);
    ASSERT_EQ(ret, 0);
  }
}

void LibZLogTest::TearDown() {
  if (log)
    delete log;
  if (context)
    delete context;
}

struct LibZLogCAPITest::Context : public UniquePoolContext {
  zlog_backend_t backend = nullptr;
  zlog_sequencer_t client = nullptr;

  ~Context() {
    if (backend)
      zlog_destroy_ceph_backend(backend);
    if (client)
      zlog_destroy_sequencer(client);
  }
};

void LibZLogCAPITest::SetUp() {
  context = new Context;
  ASSERT_NO_FATAL_FAILURE(context->Init());

  if (exclusive()) {
    // default is ok
  } else {
    int ret = zlog_create_sequencer("localhost", "5678",
        &context->client);
    ASSERT_EQ(ret, 0);
  }

  if (lowlevel()) {
    int ret = zlog_create_ceph_backend(context->ioctx,
        &context->backend);
    ASSERT_EQ(ret, 0);

    ret = zlog_create(context->backend, "c_mylog",
        context->client, &log);
    ASSERT_EQ(ret, 0);
  } else {
    const char *keys[] = {"conf_file", "pool"};
    const char *vals[] = {"", context->pool_name.c_str()};
    int ret = zlog_create_nobe("ceph", "c_mylog",
        keys, vals, 2, context->client, &log);
    ASSERT_EQ(ret, 0);
  }
}

void LibZLogCAPITest::TearDown() {
  if (log)
    zlog_destroy(log);

  if (context)
    delete context;
}
INSTANTIATE_TEST_CASE_P(Level, LibZLogTest,
    ::testing::Combine(
      ::testing::Values(true, false),
      ::testing::Values(true, false)));

INSTANTIATE_TEST_CASE_P(LevelCAPI, LibZLogCAPITest,
    ::testing::Combine(
      ::testing::Values(true, false),
      ::testing::Values(true, false)));

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
