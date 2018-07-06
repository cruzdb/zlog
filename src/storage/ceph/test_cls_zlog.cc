#include <cerrno>
#include <string>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <rados/librados.hpp>
#include "storage/ceph/protobuf_bufferlist_adapter.h"
#include "storage/ceph/cls_zlog_client.h"
#include "storage/ceph/cls_zlog.pb.h"
#include "gtest/gtest.h"
#include "port/stack_trace.h"

class ClsZlogTest : public ::testing::Test {
 protected:
  virtual void SetUp() {
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
  }

  virtual void TearDown() {
    ioctx.close();
    cluster.pool_delete(pool_name.c_str());
    cluster.shutdown();
  }

  int exec(const std::string& method, ceph::bufferlist& in,
      ceph::bufferlist& out, const std::string& oid = "obj") {
    return ioctx.exec(oid, "zlog", method.c_str(), in, out);
  }

  int entry_read(uint64_t epoch, uint64_t pos,
      ceph::bufferlist& bl, const std::string& oid = "obj") {
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, epoch, pos, 10, 1024);
    return ioctx.operate(oid, &op, &bl);
  }

  int entry_write(uint64_t epoch, uint64_t pos,
      ceph::bufferlist& bl, const std::string& oid = "obj") {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch, pos, 10, 1024, bl);
    return ioctx.operate(oid, &op);
  }

  int entry_inval(uint64_t epoch, uint64_t pos,
      bool force, const std::string& oid = "obj") {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_invalidate(op, epoch, pos, 10, 1024, force);
    return ioctx.operate(oid, &op);
  }

  int entry_seal(uint64_t epoch, const std::string& oid = "obj") {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_seal(op, epoch);
    return ioctx.operate(oid, &op);
  }

  int entry_maxpos(uint64_t epoch, uint64_t *pos, bool *empty,
      const std::string& oid = "obj") {
    int rv;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_max_position(op, epoch, pos, empty, &rv);
    int ret = ioctx.operate(oid, &op, NULL);
    return ret ? ret : rv;
  }

  int view_create(uint64_t epoch, ceph::bufferlist& bl,
      const std::string& oid = "obj") {
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_create_view(op, epoch, bl);
    return ioctx.operate(oid, &op);
  }

  int view_read(uint64_t epoch, ceph::bufferlist& bl,
      uint32_t max_views = 100, const std::string& oid = "obj") {
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_view(op, epoch, max_views);
    return ioctx.operate(oid, &op, &bl);
  }

  void decode_views(ceph::bufferlist& bl,
      std::map<uint64_t, std::string>& out) {

    std::map<uint64_t, std::string> tmp;

    zlog_ceph_proto::Views views;
    ASSERT_TRUE(decode(bl, &views));

    // unpack into return map
    for (int i = 0; i < views.views_size(); i++) {
      auto view = views.views(i);
      std::string data(view.data().c_str(), view.data().size());
      auto res = tmp.emplace(view.epoch(), data);
      (void)res;
      assert(res.second);
    }

    out.swap(tmp);
  }

  std::string pool_name;
  librados::Rados cluster;
  librados::IoCtx ioctx;
};

TEST_F(ClsZlogTest, ReadEntry_BadInput) {
  // need to create first, else we get enoent since the method is read-only.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  ret = exec("entry_read", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, ReadEntry_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, ReadEntry_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.data.header", bl);
  ASSERT_EQ(ret, 0);

  bl.clear();
  ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, ReadEntry_StaleEpoch) {
  int ret = entry_seal(1);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_seal(3);
  ASSERT_EQ(ret, 0);

  ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_read(1, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_read(2, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);
}

TEST_F(ClsZlogTest, ReadEntry_EntryDne) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -ENOENT);

  ret = entry_seal(0);
  ASSERT_EQ(ret, 0);

  ret = entry_read(0, 0, bl);
  ASSERT_EQ(ret, -ENOENT);
}

TEST_F(ClsZlogTest, ReadEntry_EntryCorrupt) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENOENT);

  bl.append("foo", strlen("foo"));
  ioctx.setxattr("obj",
      "zlog.data.entry.00000000000000000160",
      bl);

  ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, ReadEntry_InvalidEntry) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENOENT);

  ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, 0);

  ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENODATA);
}

TEST_F(ClsZlogTest, ReadEntry_InvalidEntryForced) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENOENT);

  bl.append("foo", strlen("foo"));
  ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);
  ceph::bufferlist bl2;
  ret = entry_read(0, 160, bl2);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(bl.length(), bl2.length());
  ASSERT_TRUE(memcmp(bl.c_str(), bl2.c_str(), bl.length()) == 0);

  ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, -EROFS);
  ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 160, true);
  ASSERT_EQ(ret, 0);
  ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENODATA);
}

TEST_F(ClsZlogTest, ReadEntry_SuccessUnsealed) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl2;
  ret = entry_read(0, 160, bl2);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(bl.length(), bl2.length());
  ASSERT_TRUE(memcmp(bl.c_str(), bl2.c_str(), bl.length()) == 0);
}

TEST_F(ClsZlogTest, ReadEntry_SuccessSealed) {
  int ret = entry_seal(10);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));

  ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, -ESPIPE);
  ret = entry_write(10, 160, bl);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl2;
  ret = entry_read(11, 160, bl2);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(bl.length(), bl2.length());
  ASSERT_TRUE(memcmp(bl.c_str(), bl2.c_str(), bl.length()) == 0);
}

TEST_F(ClsZlogTest, WriteEntry_BadInput) {
  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  int ret = exec("entry_write", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, WriteEntry_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, WriteEntry_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.data.header", bl);
  ASSERT_EQ(ret, 0);

  bl.clear();
  ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, WriteEntry_StaleEpoch) {
  int ret = entry_seal(1);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_seal(3);
  ASSERT_EQ(ret, 0);

  ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_write(1, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_write(2, 0, bl);
  ASSERT_EQ(ret, -ESPIPE);
}

TEST_F(ClsZlogTest, WriteEntry_EntryCorrupt) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENOENT);

  bl.append("foo", strlen("foo"));
  ioctx.setxattr("obj",
      "zlog.data.entry.00000000000000000160",
      bl);

  ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, WriteEntry_SuccessUnsealed) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, WriteEntry_SuccessSealed) {
  int ret = entry_seal(10);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));

  ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, -ESPIPE);
  ret = entry_write(10, 160, bl);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, WriteEntry_Exists) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, -EROFS);
}

TEST_F(ClsZlogTest, InvalidateEntry_BadInput) {
  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  int ret = exec("entry_invalidate", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, InvalidateEntry_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 0, true);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, InvalidateEntry_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.data.header", bl);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 0, true);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, InvalidateEntry_StaleEpoch) {
  int ret = entry_seal(1);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 0, true);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_seal(3);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 0, true);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_inval(1, 0, true);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_inval(2, 0, true);
  ASSERT_EQ(ret, -ESPIPE);
}

TEST_F(ClsZlogTest, InvalidateEntry_EntryCorrupt) {
  ceph::bufferlist bl;
  int ret = entry_read(0, 160, bl);
  ASSERT_EQ(ret, -ENOENT);

  bl.append("foo", strlen("foo"));
  ioctx.setxattr("obj",
      "zlog.data.entry.00000000000000000160",
      bl);

  ret = entry_inval(0, 160, true);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, InvalidateEntry_NoForceSuccessUnsealed) {
  int ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, InvalidateEntry_NoForceSuccessSealed) {
  int ret = entry_seal(10);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, -ESPIPE);
  ret = entry_inval(10, 160, false);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, InvalidateEntry_Idempotent) {
  int ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, 0);
  ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, InvalidateEntry_NoForceExists) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 160, false);
  ASSERT_EQ(ret, -EROFS);
}

TEST_F(ClsZlogTest, InvalidateEntry_Force) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 160, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_inval(0, 160, true);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, SealEntry_BadInput) {
  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  int ret = exec("entry_seal", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, SealEntry_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(0);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, SealEntry_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.data.header", bl);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(0);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, SealEntry_StaleEpoch) {
  int ret = entry_seal(10);
  ASSERT_EQ(ret, 0);
  for (int i = 0; i <= 10; i++) {
    ret = entry_seal(i);
    ASSERT_EQ(ret, -ESPIPE);
  }
}

TEST_F(ClsZlogTest, SealEntry_SuccessDne) {
  for (int i = 0; i < 5; i++) {
    std::stringstream oid;
    oid << "obj." << i;
    int ret = entry_seal(i);
    ASSERT_EQ(ret, 0);
  }
}

TEST_F(ClsZlogTest, SealEntry_SuccessExists) {
  int ret = entry_seal(10);
  ASSERT_EQ(ret, 0);
  for (int i = 0; i <= 10; i++) {
    ret = entry_seal(i);
    ASSERT_EQ(ret, -ESPIPE);
  }
  ret = entry_seal(11);
  ASSERT_EQ(ret, 0);
  ret = entry_seal(11);
  ASSERT_EQ(ret, -ESPIPE);
}

TEST_F(ClsZlogTest, MaxPosEntry_BadInput) {
  // need to create first, else we get enoent since the method is read-only.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  ret = exec("entry_max_position", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, MaxPosEntry_Dne) {
  uint64_t pos;
  bool empty;
  int ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -ENOENT);
}

TEST_F(ClsZlogTest, MaxPosEntry_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, MaxPosEntry_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.data.header", bl);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, MaxPosEntry_UnsealedInvalidated) {
  int ret = entry_inval(0, 0, false);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, MaxPosEntry_UnsealedWrite) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, MaxPosEntry_StaleEpoch) {
  int ret = entry_seal(4);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(0, &pos, &empty);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_maxpos(3, &pos, &empty);
  ASSERT_EQ(ret, -ESPIPE);

  ret = entry_maxpos(5, &pos, &empty);
  ASSERT_EQ(ret, -ESPIPE);
}

TEST_F(ClsZlogTest, MaxPosEntry_Empty) {
  int ret = entry_seal(4);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(4, &pos, &empty);
  ASSERT_EQ(ret, 0);
  ASSERT_TRUE(empty);
}

TEST_F(ClsZlogTest, MaxPosEntry_Write) {
  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  int ret = entry_write(0, 0, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(4);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(4, &pos, &empty);
  ASSERT_EQ(ret, 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, (unsigned)0);

  ret = entry_write(5, 160, bl);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(5);
  ASSERT_EQ(ret, 0);

  ret = entry_maxpos(5, &pos, &empty);
  ASSERT_EQ(ret, 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, (unsigned)160);
}

TEST_F(ClsZlogTest, MaxPosEntry_Invalidate) {
  int ret = entry_inval(0, 160, true);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(4);
  ASSERT_EQ(ret, 0);

  uint64_t pos;
  bool empty;
  ret = entry_maxpos(4, &pos, &empty);
  ASSERT_EQ(ret, 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, (unsigned)160);

  ret = entry_inval(4, 170, false);
  ASSERT_EQ(ret, 0);

  ret = entry_seal(5);
  ASSERT_EQ(ret, 0);

  ret = entry_maxpos(5, &pos, &empty);
  ASSERT_EQ(ret, 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, (unsigned)170);
}

TEST_F(ClsZlogTest, CreateView_BadInput) {
  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  int ret = exec("view_create", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, CreateView_Dne) {
  ceph::bufferlist bl;
  int ret = view_create(0, bl);
  ASSERT_EQ(ret, -ENOENT);
}

TEST_F(ClsZlogTest, CreateView_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);
  ceph::bufferlist bl;
  ret = view_create(0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, CreateView_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.head.header", bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, CreateView_NonZeroInitEpoch) {
  // the backend creates the object, and init_head asserts that it exists.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, "prefix");
  ret = ioctx.operate("obj", &op);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = view_create(1, bl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, CreateView_Success) {
  // the backend creates the object, and init_head asserts that it exists.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, "prefix");
  ret = ioctx.operate("obj", &op);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = view_create(0, bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(1, bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(2, bl);
  ASSERT_EQ(ret, 0);
}

TEST_F(ClsZlogTest, CreateView_InvalidNextEpoch) {
  // the backend creates the object, and init_head asserts that it exists.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, "prefix");
  ret = ioctx.operate("obj", &op);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = view_create(0, bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(1, bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(2, bl);
  ASSERT_EQ(ret, 0);

  ret = view_create(4, bl);
  ASSERT_EQ(ret, -EINVAL);

  ret = view_create(20, bl);
  ASSERT_EQ(ret, -EINVAL);

  ret = view_create(2, bl);
  ASSERT_EQ(ret, -EINVAL);

  ret = view_create(1, bl);
  ASSERT_EQ(ret, -EINVAL);

  ret = view_create(0, bl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, ReadView_BadInput) {
  // to avoid enoent on exec
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist inbl, outbl;
  inbl.append("foo", strlen("foo"));
  ret = exec("view_read", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);
}

TEST_F(ClsZlogTest, ReadView_Dne) {
  ceph::bufferlist bl;
  int ret = view_read(0, bl);
  ASSERT_EQ(ret, -ENOENT);
}

TEST_F(ClsZlogTest, ReadView_MissingHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);
  ceph::bufferlist bl;
  ret = view_read(0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, ReadView_CorruptHeader) {
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  bl.append("foo", strlen("foo"));
  ret = ioctx.setxattr("obj", "zlog.head.header", bl);
  ASSERT_EQ(ret, 0);

  ret = view_read(0, bl);
  ASSERT_EQ(ret, -EIO);
}

TEST_F(ClsZlogTest, ReadView_Empty) {
  // the backend creates the object, and init_head asserts that it exists.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, "prefix");
  ret = ioctx.operate("obj", &op);
  ASSERT_EQ(ret, 0);

  ceph::bufferlist bl;
  ret = view_read(0, bl);
  ASSERT_EQ(ret, -ENOENT);
}

TEST_F(ClsZlogTest, ReadView_Success) {
  // the backend creates the object, and init_head asserts that it exists.
  int ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);

  librados::ObjectWriteOperation op;
  zlog::cls_zlog_init_head(op, "prefix");
  ret = ioctx.operate("obj", &op);
  ASSERT_EQ(ret, 0);

  // create some views
  uint64_t epoch = 0;
  std::vector<std::string> blobs;
  for (; epoch < 10; epoch++) {
    std::stringstream ss;
    ss << "foo" << epoch;
    std::string data = ss.str();
    ceph::bufferlist bl;
    bl.append(data.c_str(), data.size());
    blobs.push_back(data);
    ret = view_create(epoch, bl);
    ASSERT_EQ(ret, 0);
  }

  // get all views
  ceph::bufferlist bl;
  std::map<uint64_t, std::string> views;
  ret = view_read(0, bl);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_EQ(views.size(), (unsigned)10);
  for (uint64_t e = 0; e < 10; e++) {
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // get 1 at a time
  for (uint64_t e = 0; e < 10; e++) {
    ceph::bufferlist bl;
    ret = view_read(e, bl, 1);
    ASSERT_EQ(ret, 0);
    decode_views(bl, views);
    ASSERT_EQ(views.size(), (unsigned)1);
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // get 4 at a time
  // 0-3
  bl.clear();
  ret = view_read(0, bl, 4);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_EQ(views.size(), (unsigned)4);
  for (uint64_t e = 0; e < 4; e++) {
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // 4-7
  bl.clear();
  ret = view_read(4, bl, 4);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_EQ(views.size(), (unsigned)4);
  for (uint64_t e = 4; e < 8; e++) {
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // 8-9
  bl.clear();
  ret = view_read(8, bl, 4);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_EQ(views.size(), (unsigned)2);
  for (uint64_t e = 8; e < 10; e++) {
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // max epoch... just to catch edge cases
  bl.clear();
  ret = view_read(9, bl);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_EQ(views.size(), (unsigned)1);
  for (uint64_t e = 9; e < 10; e++) {
    ASSERT_EQ(blobs[e], views.at(e));
  }

  // past end
  bl.clear();
  ret = view_read(10, bl);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_TRUE(views.empty());

  bl.clear();
  ret = view_read(11, bl);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_TRUE(views.empty());

  bl.clear();
  ret = view_read(33, bl);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_TRUE(views.empty());

  // requested max views 0
  bl.clear();
  ret = view_read(10, bl, 0);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_TRUE(views.empty());

  bl.clear();
  ret = view_read(0, bl, 0);
  ASSERT_EQ(ret, 0);
  decode_views(bl, views);
  ASSERT_TRUE(views.empty());
}

int main(int argc, char **argv)
{
  rocksdb::port::InstallStackTraceHandler();
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
