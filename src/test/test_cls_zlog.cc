#include <errno.h>
#include "gtest/gtest.h"
#include "libzlog/backend/cls_zlog_client.h"
#include "ceph_test_helper.h"

#define ZLOG_EPOCH_KEY "____zlog.epoch"

using namespace librados;

static librados::ObjectWriteOperation *new_op() {
  return new librados::ObjectWriteOperation();
}

static librados::ObjectReadOperation *new_rop() {
  return new librados::ObjectReadOperation();
}

TEST(ClsZlog, Seal) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "seal", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // set the first epoch value on the object to 0
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_seal(*op, 0);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // the first epoch can be set to anything (e.g. 100)
  op = new_op();
  zlog::cls_zlog_seal(*op, 100);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // epochs move strictly forward (99, 100: fail, 101: succeed)
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALID_EPOCH);

  op = new_op();
  zlog::cls_zlog_seal(*op, 100);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALID_EPOCH);

  op = new_op();
  zlog::cls_zlog_seal(*op, 101);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // seal will fail if epoch becomes corrupt
  std::map<std::string, bufferlist> vals;
  bufferlist bl;
  bl.append("j");
  vals[ZLOG_EPOCH_KEY] = bl;
  ioctx.omap_set("obj2", vals);
  op = new_op();
  zlog::cls_zlog_seal(*op, 102);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, -EIO);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, AioFill) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fill is ok if no epoch has been set
  librados::AioCompletion *c = librados::Rados::aio_create_completion();
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  int ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // set epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill(*op, 0, 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_STALE_EPOCH);
  delete c;

  // try with larger epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill(*op, 1000, 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  srand(0);

  // fill then fill is OK
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    c = librados::Rados::aio_create_completion();
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
    delete c;
  }

  std::set<uint64_t>::iterator it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    c = librados::Rados::aio_create_completion();
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
    delete c;
  }

  bufferlist bl;
  bl.append("some data");

  uint64_t maxpos = 0;

  // filling a written position yields read-only status
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    maxpos = std::max(pos, maxpos);

    if (written.count(pos))
      continue;

    written.insert(pos);
    librados::ObjectWriteOperation op;
    c = librados::Rados::aio_create_completion();
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.aio_operate("obj", c, &op);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
    delete c;
  }

  it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    c = librados::Rados::aio_create_completion();
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_READ_ONLY);
    delete c;
  }

  // fill doesn't affect max position
  uint64_t pos;
  int status;
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos-1, maxpos);

  op = new_op();
  c = librados::Rados::aio_create_completion();
  zlog::cls_zlog_fill(*op, 100, pos + 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position(op3, 99, &pos2, &status);
  ret = ioctx.operate("obj", &op3, &bl2);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, pos2);


  // fails if there is junk entry
  std::map<std::string, bufferlist> vals;
  bl.clear();
  bl.append("j");
  vals["____zlog.pos.00000000000000000099"] = bl;
  ioctx.omap_set("obj", vals);
  op = new_op();
  c = librados::Rados::aio_create_completion();
  zlog::cls_zlog_fill(*op, 100, 99);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), -EIO);
  delete c;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, Fill) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "fill", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // fill is ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_fill(*op, 0, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_fill(*op, 1000, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  srand(0);

  // fill then fill is OK
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  bufferlist bl;
  bl.append("some data");

  // filling a written position yields read-only status
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    if (written.count(pos))
      continue;

    written.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // fill doesn't affect max position
  uint64_t pos;
  int status;
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_GT(pos, (unsigned)0);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, pos + 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position(op3, 99, &pos2, &status);
  ret = ioctx.operate("obj", &op3, &bl2);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, pos2);

  // fails if there is junk entry
  std::map<std::string, bufferlist> vals;
  bl.clear();
  bl.append("j");
  vals["____zlog.pos.00000000000000000099"] = bl;
  ioctx.omap_set("obj", vals);
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EIO);

  // fill to a trimmed position returns OK
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill to a trimmed position that was previously written returns OK
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, FillInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "fill", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // fill is ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_fill(*op, 0, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_fill(*op, 1000, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  srand(0);

  // fill then fill is OK
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  bufferlist bl;
  bl.append("some data");

  // filling a written position yields read-only status
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    if (written.count(pos))
      continue;

    written.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // not sealed
  uint64_t pos;
  int status;
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, -ENOENT);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, pos + 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // not sealed
  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position(op3, 100, &pos2, &status);
  ret = ioctx.operate("obj", &op3, &bl2);
  ASSERT_EQ(ret, -ENOENT);

  // fails if there is junk entry
  std::map<std::string, bufferlist> vals;
  bl.clear();
  bl.append("j");
  vals["____zlog.pos.00000000000000000099"] = bl;
  ioctx.omap_set("obj", vals);
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EIO);

  // fill to a trimmed position returns OK
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill to a trimmed position that was previously written returns OK
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, Write) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "write", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl2;
  bl2.append("baasdf");
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_write(*op, 0, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // new max position should be correct too
  bufferlist bl5;
  uint64_t maxpos5;
  int status5;
  librados::ObjectReadOperation op5;
  zlog::cls_zlog_max_position(op5, 99, &maxpos5, &status5);
  ret = ioctx.operate("obj", &op5, &bl5);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(maxpos5, (unsigned)21);

  bufferlist bl;
  bl.append("some data");
  srand(0);

  // set epoch to 100
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj3", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // write then write -> read only status
  uint64_t max = 0;
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    // include pos = 0 first, as it tests the initialization case of the max
    // position in cls_zlog
    if (i == 0)
      pos = 0;

    if (written.count(pos))
      continue;

    if (pos > max)
      max = pos;

    written.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

    // new max position should be correct too
    bufferlist bl3;
    uint64_t maxpos;
    int status;
    librados::ObjectReadOperation op2;
    zlog::cls_zlog_max_position(op2, 99, &maxpos, &status);
    ret = ioctx.operate("obj3", &op2, &bl3);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
    
    ASSERT_EQ(maxpos-1, max);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't affect max pos
  bufferlist bl4;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation op4;
  zlog::cls_zlog_max_position(op4, 99, &pos, &status);
  ret = ioctx.operate("obj3", &op4, &bl4);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos-1, max);

  // set epoch to 100 for obj2
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill then write -> read only status
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't set max pos
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position(op2, 99, &pos, &status);
  ret = ioctx.operate("obj2", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)0);

  // writing to a trimmed position returns read-only error
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 999);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 100, 999, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // writing to a trimmed position that was previously written returns
  // read-only error
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 1000);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, AioWrite) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  bufferlist bl;
  bl.append("baasdf");

  librados::AioCompletion *c = librados::Rados::aio_create_completion();

  // ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl);
  int ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_READ_ONLY);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write(*op, 0, 20, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_STALE_EPOCH);
  delete c;

  // try with larger epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 20, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 10, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_READ_ONLY);
  delete c;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, WriteInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "write", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl2;
  bl2.append("baasdf");
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_write(*op, 0, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 19, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 1000, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  /*
   * not sealed
   */
  bufferlist bl5;
  uint64_t maxpos5;
  int status5;
  librados::ObjectReadOperation op5;
  zlog::cls_zlog_max_position(op5, 99, &maxpos5, &status5);
  ret = ioctx.operate("obj", &op5, &bl5);
  ASSERT_EQ(ret, -ENOENT);

  bufferlist bl;
  bl.append("some data");
  srand(0);

  // write then write -> read only status
  uint64_t max = 0;
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    // include pos = 0 first, as it tests the initialization case of the max
    // position in cls_zlog
    if (i == 0)
      pos = 0;

    if (written.count(pos))
      continue;

    if (pos > max)
      max = pos;

    written.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

    // not sealed
    bufferlist bl3;
    uint64_t maxpos;
    int status;
    librados::ObjectReadOperation op2;
    zlog::cls_zlog_max_position(op2, 99, &maxpos, &status);
    ret = ioctx.operate("obj3", &op2, &bl3);
    ASSERT_EQ(ret, -ENOENT);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // not sealed
  bufferlist bl4;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation op4;
  zlog::cls_zlog_max_position(op4, 99, &pos, &status);
  ret = ioctx.operate("obj3", &op4, &bl4);
  ASSERT_EQ(ret, -ENOENT);

  // fill then write -> read only status
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't set max pos
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position(op2, 100, &pos, &status);
  ret = ioctx.operate("obj2", &op2, &bl3);
  ASSERT_EQ(ret, -ENOENT);

  // writing to a trimmed position returns read-only error
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 999);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 100, 999, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // writing to a trimmed position that was previously written returns
  // read-only error
  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 1000);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, AioRead) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // ok if no epoch has been set
  librados::AioCompletion *c = librados::Rados::aio_create_completion();
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  int ret = ioctx.aio_operate("obj", c, op, &bl);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_NOT_WRITTEN);
  delete c;

  // set epoch
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_seal(*wrop, 99);
  ret = ioctx.operate("obj", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  ret = ioctx.aio_operate("obj", c, op, &bl);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_NOT_WRITTEN);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_rop();
  zlog::cls_zlog_read(*op, 0, 20);
  ret = ioctx.aio_operate("obj", c, op, &bl);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_STALE_EPOCH);
  delete c;

  srand(0);

  // cannot read from unwritten locations
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    bufferlist bl;
    c = librados::Rados::aio_create_completion();
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op, &bl);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_NOT_WRITTEN);
    delete c;
  }

  // can read stuff that was written
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    if (written.count(pos))
      continue;
    written.insert(pos);
    bufferlist bl;
    bl.append((char*)&pos, sizeof(pos));
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    c = librados::Rados::aio_create_completion();
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op, &bl);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
    ASSERT_TRUE(memcmp(bl.c_str(), &pos, sizeof(pos)) == 0);
    delete c;
  }

  wrop = new_op();
  zlog::cls_zlog_seal(*wrop, 99);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // stuff that was filled is invalid when read
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    c = librados::Rados::aio_create_completion();
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.aio_operate("obj2", c, &op, &bl);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_INVALIDATED);
    delete c;
  }

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, Read) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "read", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // set epoch
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_seal(*wrop, 99);
  ret = ioctx.operate("obj", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try with smaller epoch
  op = new_rop();
  zlog::cls_zlog_read(*op, 0, 20);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  srand(0);

  // cannot read from unwritten locations
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);
  }

  // can read stuff that was written
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    if (written.count(pos))
      continue;
    written.insert(pos);
    bufferlist bl;
    bl.append((char*)&pos, sizeof(pos));
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
    ASSERT_TRUE(memcmp(bl.c_str(), &pos, sizeof(pos)) == 0);
  }

  wrop = new_op();
  zlog::cls_zlog_seal(*wrop, 99);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // stuff that was filled is invalid when read
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj2", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);
  }

  // read from trimmed location return invalidated
  wrop = new_op();
  zlog::cls_zlog_trim(*wrop, 100, 999);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 999);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  // read from trimmed location already written return invalidated
  wrop = new_op();
  zlog::cls_zlog_write(*wrop, 100, 1000, bl);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  wrop = new_op();
  zlog::cls_zlog_trim(*wrop, 100, 1000);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 1000);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, ReadInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "read", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try again
  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try with smaller epoch
  op = new_rop();
  zlog::cls_zlog_read(*op, 0, 20);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  srand(0);

  // cannot read from unwritten locations
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);
  }

  // can read stuff that was written
  std::set<uint64_t> written;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    if (written.count(pos))
      continue;
    written.insert(pos);
    bufferlist bl;
    bl.append((char*)&pos, sizeof(pos));
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
    ASSERT_TRUE(memcmp(bl.c_str(), &pos, sizeof(pos)) == 0);
  }

  // stuff that was filled is invalid when read
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read(op, 100, pos);
    ret = ioctx.operate("obj2", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);
  }

  // read from trimmed location return invalidated
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_trim(*wrop, 100, 999);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 999);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  // read from trimmed location already written return invalidated
  wrop = new_op();
  zlog::cls_zlog_write(*wrop, 100, 1000, bl);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  wrop = new_op();
  zlog::cls_zlog_trim(*wrop, 100, 1000);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read(*op, 100, 1000);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, MaxPosition) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);


  // fails to decode input (bad message)
  ioctx.create("obj_1", true);
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj_1", "zlog", "max_position", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // set epoch
  librados::ObjectWriteOperation *wop = new_op();
  zlog::cls_zlog_seal(*wop, 99);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // epochs must be equal
  bufferlist bl;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation *rop = new_rop();
  zlog::cls_zlog_max_position(*rop, 100, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(ret, -EINVAL);

  // empty object means max pos = 0
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)0);

  // write pos 0
  wop = new_op();
  bl.clear();
  zlog::cls_zlog_write(*wop, 100, 0, bl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // next pos = 1
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)1);

  wop = new_op();
  bl.clear();
  zlog::cls_zlog_write(*wop, 100, 50, bl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // next pos = 51 after writing 50
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)51);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, Trim) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "trim", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_trim(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again. can trim unwritten position
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_trim(*op, 0, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_trim(*op, 1000, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already trimmed
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already filled
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, TrimInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "trim", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_trim(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again. can trim unwritten position
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_trim(*op, 0, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_trim(*op, 1000, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already trimmed
  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already filled
  op = new_op();
  zlog::cls_zlog_fill(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, SetProjection) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // setting > 0 as first epoch fails (object doesn't exist)
  librados::ObjectWriteOperation *op = new_op();
  bufferlist inbl;
  zlog::cls_zlog_set_projection(*op, 1, inbl);
  int ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  // setting == 0 as first epoch succeeds (object does exist)
  ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 1, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  // setting == 0 as first epoch succeeds
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 0, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, 0);

  // skipping epoch fails
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 2, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  // next epoch should be curr + 1
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 1, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, 0);

  op = new_op();
  zlog::cls_zlog_set_projection(*op, 2, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, 0);

  // skipping still fails
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 4, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  // cannot overwrite
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 0, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  op = new_op();
  zlog::cls_zlog_set_projection(*op, 1, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  op = new_op();
  zlog::cls_zlog_set_projection(*op, 2, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EINVAL);

  // ok was able to write the next one
  op = new_op();
  zlog::cls_zlog_set_projection(*op, 3, inbl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, 0);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, GetLatestProjection) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // op on non-existant object fails
  librados::ObjectReadOperation *op = new_rop();
  int opret;
  uint64_t epoch;
  bufferlist data;
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  bufferlist tmp;
  int ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -EIO);

  // op on object without a set projection fails
  ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -ENOENT);

  // set first epoch == 0
  char buf[128];
  memset(buf, 3, sizeof(buf));
  bufferlist inbl;
  inbl.append(buf, sizeof(buf));
  librados::ObjectWriteOperation *wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 0, inbl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // reading latest should return epoch = 0 and data
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_EQ(epoch, (uint64_t)0);
  ASSERT_TRUE(data == inbl);

  // set epoch = 1
  memset(buf, 4, sizeof(buf));
  inbl.clear();
  inbl.append(buf, sizeof(buf));
  wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 1, inbl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // shoudl see epoch = 1
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_EQ(epoch, (uint64_t)1);
  ASSERT_TRUE(data == inbl);

  // set epoch = 2, 3
  wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 2, inbl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  memset(buf, 7, sizeof(buf));
  inbl.clear();
  inbl.append(buf, sizeof(buf));
  wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 3, inbl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // shoudl see epoch = 3
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_EQ(epoch, (uint64_t)3);
  ASSERT_TRUE(data == inbl);

  // shoudl see epoch = 3
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_latest_projection(*op, &opret, &epoch, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_EQ(epoch, (uint64_t)3);
  ASSERT_TRUE(data == inbl);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlog, GetProjection) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // op on non-existant object fails
  librados::ObjectReadOperation *op = new_rop();
  int opret;
  bufferlist data;
  zlog::cls_zlog_get_projection(*op, &opret, 0, &data);
  bufferlist tmp;
  int ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -EIO);

  // op on object without a set projection fails
  ret = ioctx.create("obj", true);
  ASSERT_EQ(ret, 0);
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 0, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -ENOENT);

  // op on object without a set projection fails
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 1, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -ENOENT);

  // set first epoch == 0
  char buf[128];
  memset(buf, 3, sizeof(buf));
  bufferlist inbl0;
  inbl0.append(buf, sizeof(buf));
  librados::ObjectWriteOperation *wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 0, inbl0);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // reading latest should return correct data
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 0, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl0);

  // other epochs still fail
  op = new_rop();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 1, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, -ENOENT);
  ASSERT_EQ(opret, -ENOENT);

  // set epoch = 1
  memset(buf, 4, sizeof(buf));
  bufferlist inbl1;
  inbl1.append(buf, sizeof(buf));
  wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 1, inbl1);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // shoudl see epoch = 1
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 1, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl1);

  // set epoch = 2, 3
  wop = new_op();
  memset(buf, 1, sizeof(buf));
  bufferlist inbl2;
  inbl2.append(buf, sizeof(buf));
  zlog::cls_zlog_set_projection(*wop, 2, inbl2);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  memset(buf, 7, sizeof(buf));
  bufferlist inbl3;
  inbl3.append(buf, sizeof(buf));
  wop = new_op();
  zlog::cls_zlog_set_projection(*wop, 3, inbl3);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, 0);

  // shoudl see epoch = 3
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 3, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl3);

  // shoudl see epoch = 3
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 3, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl3);

  // shoudl still be able to see past epochs
  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 0, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl0);

  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 1, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl1);

  op = new_rop();
  data.clear();
  tmp.clear();
  zlog::cls_zlog_get_projection(*op, &opret, 2, &data);
  ret = ioctx.operate("obj", op, &tmp);
  ASSERT_EQ(ret, 0);
  ASSERT_EQ(opret, 0);
  ASSERT_TRUE(data == inbl2);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}
