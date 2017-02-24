/*
 * This is a copy of test_cls_zlog but swapping out the v2 calls. We should be
 * able to use some gtest features to share the majority of the code between
 * the two test suites.
 */
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

TEST(ClsZlogV2, Seal) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "seal_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // set the first epoch value on the object to 0
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_seal_v2(*op, 0);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // the first epoch can be set to anything (e.g. 100)
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 100);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // epochs move strictly forward (99, 100: fail, 101: succeed)
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALID_EPOCH);

  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 100);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALID_EPOCH);

  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 101);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // seal will fail if epoch becomes corrupt
  bufferlist bl;
  bl.append("j");
  ioctx.setxattr("obj2", ZLOG_EPOCH_KEY, bl);
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 102);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, -EIO);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, AioFill) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fill is ok if no epoch has been set
  librados::AioCompletion *c = librados::Rados::aio_create_completion();
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  int ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // set epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 0, 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_STALE_EPOCH);
  delete c;

  // try with larger epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 1000, 10);
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
    zlog::cls_zlog_fill_v2(op, 100, pos);
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
    zlog::cls_zlog_fill_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
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
    zlog::cls_zlog_fill_v2(op, 100, pos);
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
  zlog::cls_zlog_max_position_v2(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos-1, maxpos);

  op = new_op();
  c = librados::Rados::aio_create_completion();
  zlog::cls_zlog_fill_v2(*op, 100, pos + 10);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position_v2(op3, 99, &pos2, &status);
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
  zlog::cls_zlog_fill_v2(*op, 100, 99);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), -EIO);
  delete c;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, Fill) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "fill_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // fill is ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 0, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 1000, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  srand(0);

  // fill then fill is OK
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // fill doesn't affect max position
  uint64_t pos;
  int status;
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position_v2(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_GT(pos, (unsigned)0);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, pos + 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position_v2(op3, 99, &pos2, &status);
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
  zlog::cls_zlog_fill_v2(*op, 100, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EIO);

  // fill to a trimmed position returns OK
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill to a trimmed position that was previously written returns OK
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, FillInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "fill_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // fill is ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 0, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 1000, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  srand(0);

  // fill then fill is OK
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // not sealed
  uint64_t pos;
  int status;
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position_v2(op2, 99, &pos, &status);
  ret = ioctx.operate("obj", &op2, &bl3);
  ASSERT_EQ(ret, -ENOENT);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, pos + 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // not sealed
  uint64_t pos2;
  bufferlist bl2;
  librados::ObjectReadOperation op3;
  zlog::cls_zlog_max_position_v2(op3, 100, &pos2, &status);
  ret = ioctx.operate("obj", &op3, &bl2);
  ASSERT_EQ(ret, -ENOENT);

  // fails if there is junk entry
  std::map<std::string, bufferlist> vals;
  bl.clear();
  bl.append("j");
  vals["____zlog.pos.00000000000000000099"] = bl;
  ioctx.omap_set("obj", vals);
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, -EIO);

  // fill to a trimmed position returns OK
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 999);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill to a trimmed position that was previously written returns OK
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 1000);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, Write) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "write_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl2;
  bl2.append("baasdf");
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 0, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // new max position should be correct too
  bufferlist bl5;
  uint64_t maxpos5;
  int status5;
  librados::ObjectReadOperation op5;
  zlog::cls_zlog_max_position_v2(op5, 99, &maxpos5, &status5);
  ret = ioctx.operate("obj", &op5, &bl5);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(maxpos5, (unsigned)21);

  bufferlist bl;
  bl.append("some data");
  srand(0);

  // set epoch to 100
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

    // new max position should be correct too
    bufferlist bl3;
    uint64_t maxpos;
    int status;
    librados::ObjectReadOperation op2;
    zlog::cls_zlog_max_position_v2(op2, 99, &maxpos, &status);
    ret = ioctx.operate("obj3", &op2, &bl3);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
    
    ASSERT_EQ(maxpos-1, max);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't affect max pos
  bufferlist bl4;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation op4;
  zlog::cls_zlog_max_position_v2(op4, 99, &pos, &status);
  ret = ioctx.operate("obj3", &op4, &bl4);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos-1, max);

  // set epoch to 100 for obj2
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // fill then write -> read only status
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't set max pos
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position_v2(op2, 99, &pos, &status);
  ret = ioctx.operate("obj2", &op2, &bl3);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)0);

  // writing to a trimmed position returns read-only error
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 999);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 999, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // writing to a trimmed position that was previously written returns
  // read-only error
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 1000);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, AioWrite) {
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
  zlog::cls_zlog_write_v2(*op, 100, 10, bl);
  int ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 10, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_READ_ONLY);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 0, 20, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_STALE_EPOCH);
  delete c;

  // try with larger epoch
  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 20, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
  delete c;

  c = librados::Rados::aio_create_completion();
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 10, bl);
  ret = ioctx.aio_operate("obj", c, op);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_READ_ONLY);
  delete c;

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, WriteInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "write_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl2;
  bl2.append("baasdf");
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 0, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 20, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 19, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 1000, 10, bl2);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  /*
   * not sealed
   */
  bufferlist bl5;
  uint64_t maxpos5;
  int status5;
  librados::ObjectReadOperation op5;
  zlog::cls_zlog_max_position_v2(op5, 99, &maxpos5, &status5);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

    // not sealed
    bufferlist bl3;
    uint64_t maxpos;
    int status;
    librados::ObjectReadOperation op2;
    zlog::cls_zlog_max_position_v2(op2, 99, &maxpos, &status);
    ret = ioctx.operate("obj3", &op2, &bl3);
    ASSERT_EQ(ret, -ENOENT);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj3", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // not sealed
  bufferlist bl4;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation op4;
  zlog::cls_zlog_max_position_v2(op4, 99, &pos, &status);
  ret = ioctx.operate("obj3", &op4, &bl4);
  ASSERT_EQ(ret, -ENOENT);

  // fill then write -> read only status
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();

    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);
  }

  // a bunch of writes that failed didn't set max pos
  bufferlist bl3;
  librados::ObjectReadOperation op2;
  zlog::cls_zlog_max_position_v2(op2, 100, &pos, &status);
  ret = ioctx.operate("obj2", &op2, &bl3);
  ASSERT_EQ(ret, -ENOENT);

  // writing to a trimmed position returns read-only error
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 999);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 999, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  // writing to a trimmed position that was previously written returns
  // read-only error
  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 1000);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_write_v2(*op, 100, 1000, bl);
  ret = ioctx.operate("obj2", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_READ_ONLY);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, AioRead) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // ok if no epoch has been set
  librados::AioCompletion *c = librados::Rados::aio_create_completion();
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  int ret = ioctx.aio_operate("obj", c, op, &bl);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_NOT_WRITTEN);
  delete c;

  // set epoch
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_seal_v2(*wrop, 99);
  ret = ioctx.operate("obj", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  c = librados::Rados::aio_create_completion();
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  ret = ioctx.aio_operate("obj", c, op, &bl);
  ASSERT_EQ(ret, 0);
  c->wait_for_complete();
  ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_NOT_WRITTEN);
  delete c;

  // try with smaller epoch
  c = librados::Rados::aio_create_completion();
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 0, 20);
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
    zlog::cls_zlog_read_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    c = librados::Rados::aio_create_completion();
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
    ret = ioctx.aio_operate("obj", c, &op, &bl);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_OK);
    ASSERT_TRUE(memcmp(bl.c_str(), &pos, sizeof(pos)) == 0);
    delete c;
  }

  wrop = new_op();
  zlog::cls_zlog_seal_v2(*wrop, 99);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // stuff that was filled is invalid when read
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    c = librados::Rados::aio_create_completion();
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
    ret = ioctx.aio_operate("obj2", c, &op, &bl);
    ASSERT_EQ(ret, 0);
    c->wait_for_complete();
    ASSERT_EQ(c->get_return_value(), zlog::CLS_ZLOG_INVALIDATED);
    delete c;
  }

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, Read) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "read_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // set epoch
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_seal_v2(*wrop, 99);
  ret = ioctx.operate("obj", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try with smaller epoch
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 0, 20);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  srand(0);

  // cannot read from unwritten locations
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
    ret = ioctx.operate("obj", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
    ASSERT_TRUE(memcmp(bl.c_str(), &pos, sizeof(pos)) == 0);
  }

  wrop = new_op();
  zlog::cls_zlog_seal_v2(*wrop, 99);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // stuff that was filled is invalid when read
  std::set<uint64_t> filled;
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    filled.insert(pos);
    librados::ObjectWriteOperation op;
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);
  }

  // read from trimmed location return invalidated
  wrop = new_op();
  zlog::cls_zlog_trim_v2(*wrop, 100, 999);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 999);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  // read from trimmed location already written return invalidated
  wrop = new_op();
  zlog::cls_zlog_write_v2(*wrop, 100, 1000, bl);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  wrop = new_op();
  zlog::cls_zlog_trim_v2(*wrop, 100, 1000);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 1000);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, ReadInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "read_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  bufferlist bl;
  librados::ObjectReadOperation *op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try again
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  // try with smaller epoch
  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 0, 20);
  ret = ioctx.operate("obj", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_NOT_WRITTEN);

  srand(0);

  // cannot read from unwritten locations
  for (int i = 0; i < 100; i++) {
    uint64_t pos = rand();
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
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
    zlog::cls_zlog_write_v2(op, 100, pos, bl);
    ret = ioctx.operate("obj", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  std::set<uint64_t>::iterator it = written.begin();
  for (; it != written.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
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
    zlog::cls_zlog_fill_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  }

  it = filled.begin();
  for (; it != filled.end(); it++) {
    uint64_t pos = *it;
    bufferlist bl;
    librados::ObjectReadOperation op;
    zlog::cls_zlog_read_v2(op, 100, pos);
    ret = ioctx.operate("obj2", &op, &bl);
    ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);
  }

  // read from trimmed location return invalidated
  librados::ObjectWriteOperation *wrop = new_op();
  zlog::cls_zlog_trim_v2(*wrop, 100, 999);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 999);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  // read from trimmed location already written return invalidated
  wrop = new_op();
  zlog::cls_zlog_write_v2(*wrop, 100, 1000, bl);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  wrop = new_op();
  zlog::cls_zlog_trim_v2(*wrop, 100, 1000);
  ret = ioctx.operate("obj2", wrop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_rop();
  zlog::cls_zlog_read_v2(*op, 100, 1000);
  ret = ioctx.operate("obj2", op, &bl);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_INVALIDATED);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, MaxPosition) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);


  // fails to decode input (bad message)
  ioctx.create("obj_1", true);
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj_1", "zlog", "max_position_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // set epoch
  librados::ObjectWriteOperation *wop = new_op();
  zlog::cls_zlog_seal_v2(*wop, 99);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // epochs must be equal
  bufferlist bl;
  uint64_t pos;
  int status;
  librados::ObjectReadOperation *rop = new_rop();
  zlog::cls_zlog_max_position_v2(*rop, 100, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(ret, -EINVAL);

  // empty object means max pos = 0
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position_v2(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)0);

  // write pos 0
  wop = new_op();
  bl.clear();
  zlog::cls_zlog_write_v2(*wop, 100, 0, bl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // next pos = 1
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position_v2(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)1);

  wop = new_op();
  bl.clear();
  zlog::cls_zlog_write_v2(*wop, 100, 50, bl);
  ret = ioctx.operate("obj", wop);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // next pos = 51 after writing 50
  rop = new_rop();
  bl.clear();
  zlog::cls_zlog_max_position_v2(*rop, 99, &pos, &status);
  ret = ioctx.operate("obj", rop, &bl);
  ASSERT_EQ(status, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);
  ASSERT_EQ(pos, (unsigned)51);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, Trim) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "trim_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // set epoch
  op = new_op();
  zlog::cls_zlog_seal_v2(*op, 99);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again. can trim unwritten position
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 0, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_STALE_EPOCH);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 1000, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already trimmed
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already filled
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}

TEST(ClsZlogV2, TrimInit) {
  Rados cluster;
  std::string pool_name = get_temp_pool_name();
  ASSERT_EQ("", create_one_pool_pp(pool_name, cluster));
  IoCtx ioctx;
  cluster.ioctx_create(pool_name.c_str(), ioctx);

  // fails to decode input (bad message)
  bufferlist inbl, outbl;
  int ret = ioctx.exec("obj", "zlog", "trim_v2", inbl, outbl);
  ASSERT_EQ(ret, -EINVAL);

  // ok if no epoch has been set
  librados::ObjectWriteOperation *op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try again. can trim unwritten position
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 10);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with smaller epoch
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 0, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // try with larger epoch
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 1000, 20);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already trimmed
  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 100);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  // can trim a position already filled
  op = new_op();
  zlog::cls_zlog_fill_v2(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  op = new_op();
  zlog::cls_zlog_trim_v2(*op, 100, 101);
  ret = ioctx.operate("obj", op);
  ASSERT_EQ(ret, zlog::CLS_ZLOG_OK);

  ASSERT_EQ(0, destroy_one_pool_pp(pool_name, cluster));
}
