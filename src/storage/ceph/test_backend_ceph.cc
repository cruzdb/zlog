#include <iostream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "storage/test_backend.h"
#include "libzlog/test_libzlog.h"
#include "zlog/backend/ceph.h"

struct Context {
  librados::Rados cluster;
  librados::IoCtx ioctx;
  std::string pool_name;
  zlog::SeqrClient *client = nullptr;
};

void BackendTest::SetUp() {
  be_ctx = new Context;
  auto& cluster = ((Context*)be_ctx)->cluster;
  auto& ioctx = ((Context*)be_ctx)->ioctx;
  auto& pool_name = ((Context*)be_ctx)->pool_name;

  int ret = cluster.init(NULL);
  ASSERT_EQ(ret, 0);

  ret = cluster.conf_read_file(NULL);
  ASSERT_EQ(ret, 0);

  ret = cluster.connect();
  ASSERT_EQ(ret, 0);

  boost::uuids::uuid uuid = boost::uuids::random_generator()();
  pool_name = "cls_zlog_test." + boost::uuids::to_string(uuid);

  ret = cluster.pool_create(pool_name.c_str());
  ASSERT_EQ(ret, 0);

  ret = cluster.ioctx_create(pool_name.c_str(), ioctx);
  ASSERT_EQ(ret, 0);

  be = new CephBackend(&ioctx);
}

void BackendTest::TearDown() {
  if (be) {
    delete be;
  }

  if (be_ctx) {
    auto& cluster = ((Context*)be_ctx)->cluster;
    auto& ioctx = ((Context*)be_ctx)->ioctx;
    auto& pool_name = ((Context*)be_ctx)->pool_name;

    ioctx.close();
    cluster.pool_delete(pool_name.c_str());
    cluster.shutdown();

    delete (Context*)be_ctx;
  }
}

void LibZLogTest::SetUp() {
  BackendTest::SetUp();
  auto& client = ((Context*)be_ctx)->client;

  client = new zlog::SeqrClient("localhost", "5678");
  ASSERT_NO_THROW(client->Connect());

  int ret = zlog::Log::Create(be, "mylog", client, &log);
  ASSERT_EQ(ret, 0);
}

void LibZLogTest::TearDown() {
  if (log) {
    delete log;
  }

  auto client = ((Context*)be_ctx)->client;
  if (client) {
    delete client;
  }

  BackendTest::TearDown();
}
