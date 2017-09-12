#include <iostream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "zlog/backend/ceph.h"

class BackendTest::Context {
 public:
  librados::Rados cluster;
  librados::IoCtx ioctx;

  rados_t c_cluster;
  rados_ioctx_t c_ioctx;

  std::string pool_name;
};

class LibZLogTest::Context {
 public:
  std::unique_ptr<zlog::SeqrClient> client;
  zlog_sequencer_t c_client;
};

void BackendTest::SetUp() {
  context = new BackendTest::Context;

  boost::uuids::uuid uuid = boost::uuids::random_generator()();
  context->pool_name = "cls_zlog_test." + boost::uuids::to_string(uuid);

  // C++ API
  int ret = context->cluster.init(NULL);
  ASSERT_EQ(ret, 0);

  ret = context->cluster.conf_read_file(NULL);
  ASSERT_EQ(ret, 0);

  ret = context->cluster.connect();
  ASSERT_EQ(ret, 0);

  ret = context->cluster.pool_create(context->pool_name.c_str());
  ASSERT_EQ(ret, 0);

  ret = context->cluster.ioctx_create(context->pool_name.c_str(),
      context->ioctx);
  ASSERT_EQ(ret, 0);

  backend = std::unique_ptr<CephBackend>(new CephBackend(&context->ioctx));

  // C API
  ret = rados_create(&context->c_cluster, NULL);
  ASSERT_EQ(ret, 0);

  ret = rados_conf_read_file(context->c_cluster, NULL);
  ASSERT_EQ(ret, 0);

  ret = rados_connect(context->c_cluster);
  ASSERT_EQ(ret, 0);

  ret = rados_ioctx_create(context->c_cluster, context->pool_name.c_str(),
      &context->c_ioctx);
  ASSERT_EQ(ret, 0);

  ret = zlog_create_ceph_backend(context->c_ioctx, &c_backend);
  ASSERT_EQ(ret, 0);
}

void BackendTest::TearDown() {
  if (context) {
    context->ioctx.close();
    context->cluster.pool_delete(context->pool_name.c_str());
    context->cluster.shutdown();

    rados_ioctx_destroy(context->c_ioctx);
    rados_shutdown(context->c_cluster);
    zlog_destroy_ceph_backend(c_backend);

    delete context;
  }
}

void LibZLogTest::SetUp() {
  ASSERT_NO_FATAL_FAILURE(BackendTest::SetUp());

  context = new LibZLogTest::Context;

  // C++ API
  context->client = std::unique_ptr<zlog::SeqrClient>(new zlog::SeqrClient("localhost", "5678"));
  ASSERT_NO_THROW(context->client->Connect());

  zlog::Log *l;
  int ret = zlog::Log::Create(backend.get(), "mylog", context->client.get(), &l);
  ASSERT_EQ(ret, 0);

  // C API
  ret = zlog_create_sequencer("localhost", "5678", &context->c_client);
  ASSERT_EQ(ret, 0);

  ret = zlog_create(c_backend, "c_mylog", context->c_client, &c_log);
  ASSERT_EQ(ret, 0);

  log.reset(l);
}

void LibZLogTest::TearDown() {
  if (context) {
    zlog_destroy_sequencer(context->c_client);
    zlog_destroy(c_log);
    delete context;
  }
  BackendTest::TearDown();
}
