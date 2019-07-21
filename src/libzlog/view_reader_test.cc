#include "gtest/gtest.h"
#include "include/zlog/options.h"
#include "libzlog/log_backend.h"
#include "libzlog/log_impl.h"
#include "libzlog/view.h"
#include "libzlog/view_reader.h"
#include "libzlog/test_libzlog.h"

TEST(ViewReaderDeathTest, Constructor) {
  zlog::Options options;
  ASSERT_DEATH({
    zlog::ViewReader(nullptr, options);
  }, "backend.+failed");
}

TEST_F(ViewReaderTest, GetLatestView) {
  // reading from log backend will throw error because the hoid doesn't exist.
  // when we call get latest view, then no view should be returned.
  {
    auto log_backend = std::make_shared<zlog::LogBackend>(
        backend, "hoid", "prefix", "secret");
    zlog::ViewReader vr(log_backend, options);
    ASSERT_EQ(vr.get_latest_view(), nullptr);
    ASSERT_EQ(vr.view(), nullptr);
  }

  // create log: an initial view will be added
  options.error_if_exists = true;
  options.create_if_missing = true;
  options.backend = backend;
  bool created = false;
  std::shared_ptr<zlog::LogBackend> log_backend;
  int ret = zlog::create_or_open(options, "log",
      log_backend, created);
  ASSERT_EQ(ret, 0);
  ASSERT_TRUE(log_backend);
  ASSERT_TRUE(created);

  // the latest view should be epoch 1
  zlog::ViewReader vr(log_backend, options);
  const auto view1 = vr.get_latest_view();
  ASSERT_TRUE(view1);
  ASSERT_EQ(view1->epoch(), 1u);
  ASSERT_EQ(vr.view(), nullptr);

  // propose the next view
  const auto view2 = view1->expand_mapping(1000, options);
  const auto view2_data = view2->encode();
  ret = log_backend->ProposeView(2u, view2_data);
  ASSERT_EQ(ret, 0);

  // the latest view should be epoch 2
  const auto view2_read = vr.get_latest_view();
  ASSERT_TRUE(view2_read);
  ASSERT_EQ(view2_read->epoch(), 2u);
  ASSERT_EQ(vr.view(), nullptr);
}

TEST_F(ViewReaderTest, RefreshView) {
  // reading from log backend will throw error because the hoid doesn't exist.
  // when we call refresh view, then no view should be read
  {
    auto log_backend = std::make_shared<zlog::LogBackend>(
        backend, "hoid", "prefix", "secret");
    zlog::ViewReader vr(log_backend, options);
    vr.refresh_view();
    ASSERT_EQ(vr.view(), nullptr);
  }

  // create log: an initial view will be added
  options.error_if_exists = true;
  options.create_if_missing = true;
  options.backend = backend;
  bool created = false;
  std::shared_ptr<zlog::LogBackend> log_backend;
  int ret = zlog::create_or_open(options, "log",
      log_backend, created);
  ASSERT_EQ(ret, 0);
  ASSERT_TRUE(log_backend);
  ASSERT_TRUE(created);

  // the latest view should be epoch 1
  zlog::ViewReader vr(log_backend, options);
  vr.refresh_view();
  const auto view1 = vr.view();
  ASSERT_TRUE(view1);
  ASSERT_EQ(view1->epoch(), 1u);

  // propose the next view
  const auto view2 = view1->expand_mapping(1000, options);
  const auto view2_data = view2->encode();
  ret = log_backend->ProposeView(2u, view2_data);
  ASSERT_EQ(ret, 0);

  // the latest view should be epoch 2
  vr.refresh_view();
  const auto view2_read = vr.view();
  ASSERT_TRUE(view2_read);
  ASSERT_EQ(view2_read->epoch(), 2u);
}
