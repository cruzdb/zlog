#include "test_backend.h"
#include <sstream>
#include <map>
#include <set>

TEST_F(BackendTest, DeleteBeforeInit) {
  auto no_init_be = create_minimal_backend();
  no_init_be.reset();
}

TEST_F(BackendTest, UniqueId_Args) {
  uint64_t id;
  ASSERT_EQ(backend->uniqueId("", &id), -EINVAL);
  ASSERT_EQ(backend->uniqueId("a", &id), 0);
}

TEST_F(BackendTest, UniqueId) {
  std::set<uint64_t> ids;
  for (int i = 0; i < 100; i++) {
    uint64_t id;
    int ret = backend->uniqueId("hoid", &id);
    ASSERT_EQ(ret, 0);
    auto res = ids.emplace(id);
    ASSERT_TRUE(res.second);
  }
  ASSERT_EQ(ids.size(), 100u);
}

TEST_F(BackendTest, CreateLog_Args) {
  std::string s;
  ASSERT_EQ(backend->CreateLog("", "", &s, &s), -EINVAL);
  ASSERT_EQ(backend->CreateLog("a", "", &s, &s), 0);
  ASSERT_EQ(backend->CreateLog("b", "a", &s, &s), 0);
  ASSERT_EQ(backend->CreateLog("c", "a", nullptr, &s), 0);
  ASSERT_EQ(backend->CreateLog("d", "a", nullptr, nullptr), 0);
}

TEST_F(BackendTest, CreateLog_Exclusive) {
  std::string s;
  ASSERT_EQ(backend->CreateLog("a", "", &s, &s), 0);
  ASSERT_EQ(backend->CreateLog("a", "", &s, &s), -EEXIST);
}

TEST_F(BackendTest, CreateLog_HoidPrefix) {
  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);
  ASSERT_FALSE(hoid.empty());
  ASSERT_FALSE(prefix.empty());
  ASSERT_NE(hoid, prefix);
  ASSERT_NE(hoid, "a");
  ASSERT_NE(prefix, "a");

  ASSERT_EQ(backend->CreateLog("b", "", &hoid, nullptr), 0);
  ASSERT_FALSE(hoid.empty());

  ASSERT_EQ(backend->CreateLog("c", "", nullptr, &prefix), 0);
  ASSERT_FALSE(prefix.empty());
}

TEST_F(BackendTest, OpenLog_Args) {
  std::string s;
  ASSERT_EQ(backend->OpenLog("", &s, &s), -EINVAL);
  ASSERT_EQ(backend->CreateLog("a", "", &s, &s), 0);
  ASSERT_EQ(backend->OpenLog("a", &s, &s), 0);
  ASSERT_EQ(backend->OpenLog("a", nullptr, &s), 0);
  ASSERT_EQ(backend->OpenLog("a", nullptr, nullptr), 0);
}

TEST_F(BackendTest, OpenLog_Dne) {
  std::string s;
  ASSERT_EQ(backend->OpenLog("a", &s, &s), -ENOENT);
}

TEST_F(BackendTest, OpenLog_HoidPrefix) {
  std::string hoid0, prefix0;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid0, &prefix0), 0);

  std::string hoid, prefix;
  ASSERT_EQ(backend->OpenLog("a", &hoid, &prefix), 0);
  ASSERT_EQ(hoid, hoid0);
  ASSERT_EQ(prefix, prefix0);
  ASSERT_FALSE(hoid.empty());
  ASSERT_FALSE(prefix.empty());
  ASSERT_NE(hoid, prefix);
  ASSERT_NE(hoid, "a");
  ASSERT_NE(prefix, "a");

  hoid = "abc0";
  prefix = "abc1";
  ASSERT_EQ(backend->OpenLog("b", &hoid, nullptr), -ENOENT);
  ASSERT_EQ(hoid, "abc0");

  ASSERT_EQ(backend->OpenLog("c", nullptr, &prefix), -ENOENT);
  ASSERT_EQ(prefix, "abc1");
}

TEST_F(BackendTest, ProposeView_Args) {
  ASSERT_EQ(backend->ProposeView("", 1, "b"), -EINVAL);
  ASSERT_EQ(backend->ProposeView("", 2, "b"), -EINVAL);

  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);

  ASSERT_EQ(backend->ProposeView(hoid, 2, "b"), 0);
  ASSERT_EQ(backend->ProposeView(hoid, 0, "b"), -EINVAL);
  ASSERT_EQ(backend->ProposeView(hoid, 3, ""), 0);
}

TEST_F(BackendTest, ProposeView_NoInit) {
  ASSERT_EQ(backend->ProposeView("a", 0, ""), -EINVAL);
  ASSERT_EQ(backend->ProposeView("a", 2, ""), -ENOENT);
  ASSERT_EQ(backend->ProposeView("a", 1, ""), -ENOENT);
  ASSERT_EQ(backend->ProposeView("a", 3, ""), -ENOENT);
}

TEST_F(BackendTest, ProposeView_Epoch) {
  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);

  ASSERT_EQ(backend->ProposeView(hoid, 1, ""), -ESPIPE);
  ASSERT_EQ(backend->ProposeView(hoid, 2, ""), 0);
  ASSERT_EQ(backend->ProposeView(hoid, 3, ""), 0);
  ASSERT_EQ(backend->ProposeView(hoid, 5, ""), -EINVAL);
  ASSERT_EQ(backend->ProposeView(hoid, 6, ""), -EINVAL);
  ASSERT_EQ(backend->ProposeView(hoid, 3, ""), -ESPIPE);
  ASSERT_EQ(backend->ProposeView(hoid, 6000, ""), -EINVAL);
  ASSERT_EQ(backend->ProposeView(hoid, 5, ""), -EINVAL);
  ASSERT_EQ(backend->ProposeView(hoid, 4, ""), 0);
  ASSERT_EQ(backend->ProposeView(hoid, 2, ""), -ESPIPE);
  ASSERT_EQ(backend->ProposeView(hoid, 3, ""), -ESPIPE);
  ASSERT_EQ(backend->ProposeView(hoid, 1, ""), -ESPIPE);

  ASSERT_EQ(backend->CreateLog("b", "", &hoid, &prefix), 0);

  ASSERT_EQ(backend->ProposeView(hoid, 2, ""), 0);
  ASSERT_EQ(backend->ProposeView(hoid, 1, ""), -ESPIPE);
  ASSERT_EQ(backend->ProposeView(hoid, 3, ""), 0);
}

TEST_F(BackendTest, ReadViews_Args) {
  std::map<uint64_t, std::string> views;
  ASSERT_EQ(backend->ReadViews("", 1, 1, &views), -EINVAL);

  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);
  ASSERT_EQ(backend->ReadViews(hoid, 0, 1, &views), -EINVAL);
  ASSERT_EQ(backend->ReadViews(hoid, 1, 1, &views), 0);
}

TEST_F(BackendTest, ReadViews_NoInit) {
  std::map<uint64_t, std::string> views;
  ASSERT_EQ(backend->ReadViews("a", 1, 1, &views), -ENOENT);
}

TEST_F(BackendTest, ReadViews_ZeroMax) {
  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);

  std::map<uint64_t, std::string> views;
  ASSERT_EQ(backend->ReadViews(hoid, 1, 1, &views), 0);
  ASSERT_EQ(views.size(), 1u);

  views.clear();
  ASSERT_EQ(backend->ReadViews(hoid, 1, 0, &views), 0);
  ASSERT_EQ(views.size(), 0u);
}

TEST_F(BackendTest, ReadViews) {
  std::string hoid, prefix;
  ASSERT_EQ(backend->CreateLog("a", "", &hoid, &prefix), 0);

  std::map<uint64_t, std::string> views;
  ASSERT_EQ(backend->ReadViews(hoid, 1, 1, &views), 0);
  ASSERT_EQ(views.size(), 1u);

  std::map<uint64_t, std::string> truth_views;
  for (int i = 2; i <= 10; i++) {
    std::stringstream ss;
    ss << i;
    truth_views[i] = ss.str();
    ASSERT_EQ(backend->ProposeView(hoid, i, ss.str()), 0);
  }

  ASSERT_EQ(backend->ReadViews(hoid, 1, 20, &views), 0);
  ASSERT_EQ(views.size(), 10u);

  for (int i = 1; i <= 10; i++) {
    ASSERT_EQ(backend->ReadViews(hoid, i, 20, &views), 0);
    ASSERT_EQ(views.size(), (10u - i + 1));
    for (auto it : views) {
      ASSERT_EQ(it.second, truth_views[it.first]);
    }
  }

  ASSERT_EQ(backend->ReadViews(hoid, 11, 1, &views), 0);
  ASSERT_TRUE(views.empty());

  ASSERT_EQ(backend->ReadViews(hoid, 12, 1, &views), 0);
  ASSERT_TRUE(views.empty());

  ASSERT_EQ(backend->ReadViews(hoid, 10, 1, &views), 0);
  ASSERT_EQ(views.size(), 1u);

  ASSERT_EQ(backend->ReadViews(hoid, 1, 12, &views), 0);
  ASSERT_EQ(views.size(), 10u);
  ASSERT_EQ(views, truth_views);

  ASSERT_EQ(backend->ReadViews(hoid, 0, 1, &views), -EINVAL);
}

TEST_F(BackendTest, Write_Args) {
  ASSERT_EQ(backend->Write("", "", 1, 0), -EINVAL);

  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Write("a", "", 0, 0), -EINVAL);
}

TEST_F(BackendTest, Write_NoInit) {
  ASSERT_EQ(backend->Write("a", "", 1, 0), -ENOENT);
  ASSERT_EQ(backend->Write("a", "", 2, 0), -ENOENT);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 2, 1), 0);
}

TEST_F(BackendTest, Write_StaleEpoch) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Write("a", "", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 2, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 3, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 9, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 10, 1), 0);
  ASSERT_EQ(backend->Write("a", "", 11, 2), 0);
  ASSERT_EQ(backend->Write("a", "", 110, 3), 0);
  ASSERT_EQ(backend->Write("a", "", 7, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Write("a", "", 0, 0), -EINVAL);
}

TEST_F(BackendTest, Write_PosExists) {
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 0), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 1, 0), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 1, 1), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 2), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 3), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 1), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 1, 3), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 1, 2), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 10, 1), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 10, 3), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 10, 2), -EROFS);
  ASSERT_EQ(backend->Write("a", "", 10, 4), 0);
  ASSERT_EQ(backend->Seal("a", 4), 0);
  ASSERT_EQ(backend->Write("a", "", 3, 4), -ESPIPE);
}

TEST_F(BackendTest, Write_TrimFill) {
  ASSERT_EQ(backend->Seal("a", 1), 0);

  ASSERT_EQ(backend->Write("a", "", 1, 0), 0);
  ASSERT_EQ(backend->Fill("a", 1, 0), -EROFS);

  ASSERT_EQ(backend->Fill("a", 1, 1), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 1), -EROFS);

  ASSERT_EQ(backend->Write("a", "", 1, 2), 0);
  ASSERT_EQ(backend->Trim("a", 1, 2), 0);

  ASSERT_EQ(backend->Trim("a", 1, 3), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 3), -EROFS);
}

TEST_F(BackendTest, Write_MaxPos) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->Seal("a", 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_TRUE(empty);

  ASSERT_EQ(backend->Write("a", "", 1, 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 1u);

  ASSERT_EQ(backend->Write("a", "", 1, 5), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5u);

  ASSERT_EQ(backend->Write("a", "", 1, 5000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);

  ASSERT_EQ(backend->Write("a", "", 1, 4000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);
}

TEST_F(BackendTest, Read_Args) {
  std::string data;
  ASSERT_EQ(backend->Read("", 1, 0, &data), -EINVAL);

  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Read("a", 0, 0, &data), -EINVAL);
}

TEST_F(BackendTest, Read_NoInit) {
  std::string data;
  ASSERT_EQ(backend->Read("a", 1, 0, &data), -ENOENT);
  ASSERT_EQ(backend->Read("a", 2, 1, &data), -ENOENT);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Read("a", 1, 0, &data), -ERANGE);
  ASSERT_EQ(backend->Read("a", 2, 1, &data), -ERANGE);
  ASSERT_EQ(backend->Write("a", "", 1, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 1, 1), 0);
  ASSERT_EQ(backend->Read("a", 1, 0, &data), 0);
  ASSERT_EQ(backend->Read("a", 2, 1, &data), 0);
}

TEST_F(BackendTest, Read_StaleEpoch) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 1), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 2), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 3), 0);

  std::string data;
  ASSERT_EQ(backend->Read("a", 10, 0, &data), 0);
  ASSERT_EQ(backend->Read("a", 0, 0, &data), -EINVAL);
  ASSERT_EQ(backend->Read("a", 1, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 2, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 3, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 9, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(backend->Read("a", 11, 2, &data), 0);
  ASSERT_EQ(backend->Read("a", 110, 3, &data), 0);
  ASSERT_EQ(backend->Read("a", 7, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 1, 0, &data), -ESPIPE);
  ASSERT_EQ(backend->Read("a", 0, 0, &data), -EINVAL);
}

TEST_F(BackendTest, Read_NoPos) {
  ASSERT_EQ(backend->Seal("a", 10), 0);

  std::string data;
  ASSERT_EQ(backend->Read("a", 10, 0, &data), -ERANGE);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), -ERANGE);
  ASSERT_EQ(backend->Read("a", 10, 2, &data), -ERANGE);
  ASSERT_EQ(backend->Write("a", "", 10, 0), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 1), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 2), 0);
  ASSERT_EQ(backend->Read("a", 10, 0, &data), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(backend->Read("a", 10, 2, &data), 0);
  ASSERT_EQ(backend->Read("a", 11, 0, &data), 0);
  ASSERT_EQ(backend->Read("a", 12, 1, &data), 0);
  ASSERT_EQ(backend->Read("a", 13, 2, &data), 0);
  ASSERT_EQ(backend->Read("a", 3, 2, &data), -ESPIPE);
}

TEST_F(BackendTest, Read) {
  std::string data;
  ASSERT_EQ(backend->Seal("a", 10), 0);

  ASSERT_EQ(backend->Write("a", "", 10, 0), 0);
  ASSERT_EQ(backend->Read("a", 10, 0, &data), 0);
  ASSERT_EQ(data, "");

  ASSERT_EQ(backend->Write("a", "abc", 10, 1), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(data, "abc");

  ASSERT_EQ(backend->Read("a", 10, 0, &data), 0);
  ASSERT_EQ(data, "");
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(data, "abc");
}

TEST_F(BackendTest, Read_FillTrim) {
  std::string data;
  ASSERT_EQ(backend->Seal("a", 10), 0);

  ASSERT_EQ(backend->Write("a", "", 10, 0), 0);
  ASSERT_EQ(backend->Read("a", 10, 0, &data), 0);
  ASSERT_EQ(data, "");

  ASSERT_EQ(backend->Fill("a", 10, 1), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), -ENODATA);

  ASSERT_EQ(backend->Fill("a", 10, 19), 0);
  ASSERT_EQ(backend->Read("a", 10, 19, &data), -ENODATA);

  ASSERT_EQ(backend->Trim("a", 10, 0), 0);
  ASSERT_EQ(backend->Read("a", 10, 0, &data), -ENODATA);

  ASSERT_EQ(backend->Trim("a", 10, 19), 0);
  ASSERT_EQ(backend->Read("a", 10, 19, &data), -ENODATA);

  ASSERT_EQ(backend->Trim("a", 10, 10), 0);
  ASSERT_EQ(backend->Read("a", 10, 10, &data), -ENODATA);
}

TEST_F(BackendTest, Fill_Args) {
  ASSERT_EQ(backend->Fill("", 1, 0), -EINVAL);

  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Fill("a", 0, 0), -EINVAL);
}

TEST_F(BackendTest, Fill_NoInit) {
  ASSERT_EQ(backend->Fill("a", 1, 0), -ENOENT);
  ASSERT_EQ(backend->Fill("a", 2, 1), -ENOENT);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Fill("a", 1, 0), 0);
  ASSERT_EQ(backend->Fill("a", 2, 1), 0);
}

TEST_F(BackendTest, Fill_StaleEpoch) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Fill("a", 10, 0), 0);
  ASSERT_EQ(backend->Fill("a", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Fill("a", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 2, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 3, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 9, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 10, 1), 0);
  ASSERT_EQ(backend->Fill("a", 11, 2), 0);
  ASSERT_EQ(backend->Fill("a", 110, 3), 0);
  ASSERT_EQ(backend->Fill("a", 7, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Fill("a", 0, 0), -EINVAL);

  ASSERT_EQ(backend->Seal("b", 1), 0);
  ASSERT_EQ(backend->Fill("b", 10, 0), 0);
  ASSERT_EQ(backend->Fill("b", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Fill("b", 1, 0), 0);

  ASSERT_EQ(backend->Seal("c", 2), 0);
  ASSERT_EQ(backend->Fill("c", 10, 0), 0);
  ASSERT_EQ(backend->Fill("c", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Fill("c", 2, 0), 0);
  ASSERT_EQ(backend->Fill("c", 1, 0), -ESPIPE);
}

TEST_F(BackendTest, Fill_Idempotent) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Fill("a", 10, 1), 0);
  ASSERT_EQ(backend->Fill("a", 10, 1), 0);
}

TEST_F(BackendTest, Fill_NoOverwrite) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 1), 0);
  ASSERT_EQ(backend->Fill("a", 10, 1), -EROFS);
}

TEST_F(BackendTest, Fill_NoRead) {
  std::string data;
  ASSERT_EQ(backend->Seal("a", 10), 0);

  ASSERT_EQ(backend->Write("a", "lala", 10, 1), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(data, "lala");

  ASSERT_EQ(backend->Fill("a", 10, 2), 0);
  ASSERT_EQ(backend->Read("a", 10, 2, &data), -ENODATA);
}

TEST_F(BackendTest, Fill_MaxPos) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->Seal("a", 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_TRUE(empty);

  ASSERT_EQ(backend->Fill("a", 1, 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 1u);

  ASSERT_EQ(backend->Fill("a", 1, 5), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5u);

  ASSERT_EQ(backend->Fill("a", 1, 5000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);

  ASSERT_EQ(backend->Fill("a", 1, 4000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);
}

TEST_F(BackendTest, Trim_Args) {
  ASSERT_EQ(backend->Trim("", 1, 0), -EINVAL);

  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Trim("a", 0, 0), -EINVAL);
}

TEST_F(BackendTest, Trim_NoInit) {
  ASSERT_EQ(backend->Trim("a", 1, 0), -ENOENT);
  ASSERT_EQ(backend->Trim("a", 2, 1), -ENOENT);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Trim("a", 1, 0), 0);
  ASSERT_EQ(backend->Trim("a", 2, 1), 0);
}

TEST_F(BackendTest, Trim_StaleEpoch) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Trim("a", 10, 0), 0);
  ASSERT_EQ(backend->Trim("a", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Trim("a", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 2, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 3, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 9, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 10, 1), 0);
  ASSERT_EQ(backend->Trim("a", 11, 2), 0);
  ASSERT_EQ(backend->Trim("a", 110, 3), 0);
  ASSERT_EQ(backend->Trim("a", 7, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 1, 0), -ESPIPE);
  ASSERT_EQ(backend->Trim("a", 0, 0), -EINVAL);

  ASSERT_EQ(backend->Seal("b", 1), 0);
  ASSERT_EQ(backend->Trim("b", 10, 0), 0);
  ASSERT_EQ(backend->Trim("b", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Trim("b", 1, 0), 0);

  ASSERT_EQ(backend->Seal("c", 2), 0);
  ASSERT_EQ(backend->Trim("c", 10, 0), 0);
  ASSERT_EQ(backend->Trim("c", 0, 0), -EINVAL);
  ASSERT_EQ(backend->Trim("c", 2, 0), 0);
  ASSERT_EQ(backend->Trim("c", 1, 0), -ESPIPE);
}

TEST_F(BackendTest, Trim_Idempotent) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Trim("a", 10, 1), 0);
  ASSERT_EQ(backend->Trim("a", 10, 1), 0);
}

TEST_F(BackendTest, Trim_Overwrite) {
  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Write("a", "", 10, 1), 0);
  ASSERT_EQ(backend->Trim("a", 10, 1), 0);
}

TEST_F(BackendTest, Trim_NoRead) {
  std::string data;
  ASSERT_EQ(backend->Seal("a", 10), 0);

  ASSERT_EQ(backend->Write("a", "lala", 10, 1), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), 0);
  ASSERT_EQ(data, "lala");

  ASSERT_EQ(backend->Trim("a", 10, 2), 0);
  ASSERT_EQ(backend->Read("a", 10, 2, &data), -ENODATA);

  ASSERT_EQ(backend->Trim("a", 10, 1), 0);
  ASSERT_EQ(backend->Read("a", 10, 1, &data), -ENODATA);
}

TEST_F(BackendTest, Trim_Fill) {
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Fill("a", 1, 10), 0);
  ASSERT_EQ(backend->Trim("a", 1, 10), 0);

  ASSERT_EQ(backend->Seal("b", 1), 0);
  ASSERT_EQ(backend->Trim("b", 1, 10), 0);
  ASSERT_EQ(backend->Fill("b", 1, 10), 0);
}

TEST_F(BackendTest, Trim_MaxPos) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->Seal("a", 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_TRUE(empty);

  ASSERT_EQ(backend->Trim("a", 1, 1), 0);

  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 1u);

  ASSERT_EQ(backend->Trim("a", 1, 5), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5u);

  ASSERT_EQ(backend->Trim("a", 1, 5000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);

  ASSERT_EQ(backend->Trim("a", 1, 4000), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 5000u);
}

TEST_F(BackendTest, Seal_Args) {
  ASSERT_EQ(backend->Seal("", 1), -EINVAL);
  ASSERT_EQ(backend->Seal("a", 0), -EINVAL);
  ASSERT_EQ(backend->Seal("a", 1), 0);
}

TEST_F(BackendTest, Seal) {
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->Seal("a", 1), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 1), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 2), 0);
  ASSERT_EQ(backend->Seal("a", 3), 0);
  ASSERT_EQ(backend->Seal("a", 4), 0);
  ASSERT_EQ(backend->Seal("a", 4), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 2), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 3), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 1), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 0), -EINVAL);

  ASSERT_EQ(backend->Seal("a", 10), 0);
  ASSERT_EQ(backend->Seal("a", 10), -ESPIPE);

  ASSERT_EQ(backend->Seal("a", 11), 0);
  ASSERT_EQ(backend->Seal("a", 20), 0);
  ASSERT_EQ(backend->Seal("a", 20), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 10), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 9), -ESPIPE);
  ASSERT_EQ(backend->Seal("a", 21), 0);
}

TEST_F(BackendTest, MaxPos_Args) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->MaxPos("", 1, &pos, &empty), -EINVAL);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->MaxPos("a", 0, &pos, &empty), -EINVAL);
}

TEST_F(BackendTest, MaxPos_NoInit) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), -ENOENT);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), -ENOENT);
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
}

TEST_F(BackendTest, MaxPos_InvalidEpoch) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->Seal("a", 1), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_EQ(backend->MaxPos("a", 2, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 3, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_EQ(backend->MaxPos("a", 2, &pos, &empty), -ESPIPE);

  ASSERT_EQ(backend->Seal("a", 3), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 2, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 4, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 3, &pos, &empty), 0);
  ASSERT_EQ(backend->MaxPos("a", 4, &pos, &empty), -ESPIPE);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), -ESPIPE);
}

TEST_F(BackendTest, MaxPos) {
  bool empty;
  uint64_t pos;
  ASSERT_EQ(backend->Seal("a", 1), 0);

  pos = 99999;
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_TRUE(empty);
  ASSERT_EQ(pos, 99999u);

  ASSERT_EQ(backend->Write("a", "", 1, 1), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 1u);

  ASSERT_EQ(backend->Write("a", "", 1, 20), 0);
  ASSERT_EQ(backend->MaxPos("a", 1, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 20u);

  ASSERT_EQ(backend->Seal("a", 19), 0);

  ASSERT_EQ(backend->Write("a", "", 19, 200000000), 0);
  ASSERT_EQ(backend->MaxPos("a", 19, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 200000000u);

  ASSERT_EQ(backend->Write("a", "", 19, 30), 0);
  ASSERT_EQ(backend->MaxPos("a", 19, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 200000000u);

  ASSERT_EQ(backend->Write("a", "", 19, 16), 0);
  ASSERT_EQ(backend->MaxPos("a", 19, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 200000000u);

  ASSERT_EQ(backend->Write("a", "", 19, 200000001), 0);
  ASSERT_EQ(backend->MaxPos("a", 19, &pos, &empty), 0);
  ASSERT_FALSE(empty);
  ASSERT_EQ(pos, 200000001u);
}

TEST_F(BackendTest, ListHeads_Empty) {
  std::vector<std::string> output;
  ASSERT_EQ(backend->ListHeads(output), 0);
  ASSERT_EQ(output.size(), 0u);
}

TEST_F(BackendTest, ListHeads) {
  std::string hoid;
  std::vector<std::string> expected;

  ASSERT_EQ(backend->CreateLog("log1", "", &hoid, nullptr), 0);
  expected.emplace_back(hoid);
  ASSERT_EQ(backend->CreateLog("another_log", "", &hoid, nullptr), 0);
  expected.emplace_back(hoid);
  ASSERT_EQ(backend->CreateLog("lastOne", "", &hoid, nullptr), 0);
  expected.emplace_back(hoid);

  std::sort(expected.begin(), expected.end());
  
  std::vector<std::string> output;
  ASSERT_EQ(backend->ListHeads(output), 0);
  ASSERT_EQ(output, expected);
}

TEST_F(BackendTest, ListLinks_Empty) {
  std::vector<std::string> output;
  ASSERT_EQ(backend->ListHeads(output), 0);
  ASSERT_EQ(output.size(), 0u);
}

TEST_F(BackendTest, ListLinks) {
  ASSERT_EQ(backend->CreateLog("log1", "", nullptr, nullptr), 0);
  ASSERT_EQ(backend->CreateLog("another_log", "", nullptr, nullptr), 0);
  ASSERT_EQ(backend->CreateLog("lastOne", "", nullptr, nullptr), 0);

  std::vector<std::string> expected = { "head.another_log", "head.lastOne", "head.log1" };

  std::vector<std::string> output;
  ASSERT_EQ(backend->ListLinks(output), 0);
  ASSERT_EQ(output, expected);
}
