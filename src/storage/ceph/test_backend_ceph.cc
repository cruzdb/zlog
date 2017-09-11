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
  std::string pool_name;
};

class LibZLogTest::Context {
 public:
  std::unique_ptr<zlog::SeqrClient> client;
};

void BackendTest::SetUp() {
  context = new BackendTest::Context;

  int ret = context->cluster.init(NULL);
  ASSERT_EQ(ret, 0);

  ret = context->cluster.conf_read_file(NULL);
  ASSERT_EQ(ret, 0);

  ret = context->cluster.connect();
  ASSERT_EQ(ret, 0);

  boost::uuids::uuid uuid = boost::uuids::random_generator()();
  context->pool_name = "cls_zlog_test." + boost::uuids::to_string(uuid);

  ret = context->cluster.pool_create(context->pool_name.c_str());
  ASSERT_EQ(ret, 0);

  ret = context->cluster.ioctx_create(context->pool_name.c_str(),
      context->ioctx);
  ASSERT_EQ(ret, 0);

  backend = std::unique_ptr<CephBackend>(new CephBackend(&context->ioctx));
}

void BackendTest::TearDown() {
  if (context) {
    context->ioctx.close();
    context->cluster.pool_delete(context->pool_name.c_str());
    context->cluster.shutdown();
    delete context;
  }
}

void LibZLogTest::SetUp() {
  ASSERT_NO_FATAL_FAILURE(BackendTest::SetUp());

  context = new LibZLogTest::Context;

  context->client = std::unique_ptr<zlog::SeqrClient>(
      new zlog::SeqrClient("localhost", "5678"));
  ASSERT_NO_THROW(context->client->Connect());

  zlog::Log *l;
  int ret = zlog::Log::Create(backend.get(), "mylog",
      context->client.get(), &l);
  ASSERT_EQ(ret, 0);

  log.reset(l);
}

void LibZLogTest::TearDown() {
  if (context) {
    delete context;
  }
  BackendTest::TearDown();
}
