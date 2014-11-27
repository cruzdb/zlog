#include <string>
#include <cstdlib>
#include <sstream>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <boost/thread/thread.hpp>
#include <rados/librados.hpp>
#include <gtest/gtest.h>
#include "../../zstate/objects/register.h"

static std::string randstr(void)
{
    std::stringstream ss;
    ss << boost::uuids::random_generator()();
    return ss.str();
}

static void make_context(librados::Rados& rados, librados::IoCtx& ioctx)
{
  assert(!rados.init(NULL));
  assert(!rados.conf_read_file(NULL));
  assert(!rados.connect());

  std::stringstream ss;
  ss << boost::uuids::random_generator()();
  std::string pool = ss.str();

  rados.pool_create("contrail");
  assert(!rados.ioctx_create("contrail", ioctx));
}

static void get_log(librados::IoCtx& ioctx, zlog::Log& log, std::string name,
    zlog::SeqrClient *client)
{
  int ret = zlog::Log::OpenOrCreate(ioctx, name, 13, client, log);
  ASSERT_EQ(ret, 0);
}

TEST(Register, DefaultValue) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  make_context(rados, ioctx);

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  std::string log_name = randstr();
  zlog::Log log;
  get_log(ioctx, log, log_name, &client);

  Register reg(log);

  int value;
  ASSERT_EQ(0, reg.read(&value));
  ASSERT_EQ(0, value);
}

TEST(Register, Basic) {
  librados::Rados rados;
  librados::IoCtx ioctx;
  make_context(rados, ioctx);

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  std::string log_name = randstr();

  zlog::Log log;
  get_log(ioctx, log, log_name, &client);

  Register reg(log);

  int value;
  ASSERT_EQ(0, reg.write(5));
  ASSERT_EQ(0, reg.read(&value));
  ASSERT_EQ(5, value);
  ASSERT_EQ(0, reg.write(5));
  ASSERT_EQ(0, reg.write(500));
  ASSERT_EQ(0, reg.write(333));
  ASSERT_EQ(0, reg.read(&value));
  ASSERT_EQ(333, value);
}

static void thrash_log(librados::Rados *rados, std::string pool_name, std::string log_name)
{
  librados::IoCtx ioctx;
  assert(!rados->ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::Log log;
  get_log(ioctx, log, log_name, &client);

  Register reg(log);

  for (int i = 0; i < 100; i++) {
    int value = std::rand() + 1; // ensure positive
    ASSERT_EQ(0, reg.write(value));
    ASSERT_EQ(0, reg.read(&value));
  }
}

TEST(Register, MultiThreaded) {
  librados::Rados rados;
  assert(!rados.init(NULL));
  assert(!rados.conf_read_file(NULL));
  assert(!rados.connect());

  std::string pool_name = "contrail";
  rados.pool_create(pool_name.c_str());

  std::string log_name = randstr();

  librados::IoCtx ioctx;
  assert(!rados.ioctx_create(pool_name.c_str(), ioctx));

  zlog::SeqrClient client("localhost", "5678");
  ASSERT_NO_THROW(client.Connect());

  zlog::Log log;
  get_log(ioctx, log, log_name, &client);

  boost::thread_group threads;
  for (int i = 0; i < 3; i++) {
    boost::thread *t = new boost::thread(thrash_log, &rados, pool_name, log_name);
    threads.add_thread(t);
  }

  threads.join_all();

  Register reg(log);

  int value;
  ASSERT_EQ(0, reg.read(&value));
  ASSERT_LT(0, value);

  ASSERT_EQ(0, reg.write(10));
  ASSERT_EQ(0, reg.read(&value));
  ASSERT_EQ(10, value);
}
