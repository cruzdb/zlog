#include "gtest/gtest.h"
#include "include/zlog/options.h"
#include "libzlog/object_map.h"

TEST(ObjectMapDeathTest, Constructor) {
  ASSERT_DEATH({
    zlog::ObjectMap(1, {}, 0);
  }, "valid.+failed");
  ASSERT_DEATH({
    zlog::ObjectMap(2, {}, 0);
  }, "valid.+failed");

  // first stripe isn't zero
  ASSERT_DEATH({
    zlog::ObjectMap(1,
        {{1, zlog::MultiStripe(0, 1, 1, 0, 1, 0)}},
        0);
  }, "valid.+failed");

  // invalid next_stripe_id
  ASSERT_DEATH({
    zlog::ObjectMap(2,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)}},
        0);
  }, "valid.+failed");

  // second stripe min pos doesn't equal 1 / the index key
  ASSERT_DEATH({
    zlog::ObjectMap(2,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)},
         {1, zlog::MultiStripe(1, 1, 2, 2, 1, 3)}},
        0);
  }, "valid.+failed");

  // base id of next stripe doesn't follow prev stripe
  ASSERT_DEATH({
    zlog::ObjectMap(2,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)},
         {1, zlog::MultiStripe(2, 1, 1, 1, 1, 1)}},
        0);
  }, "valid.+failed");
  ASSERT_DEATH({
    zlog::ObjectMap(3,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)},
         {1, zlog::MultiStripe(2, 1, 1, 1, 1, 1)}},
        0);
  }, "valid.+failed");
}

TEST(ObjectMapDeathTest, StripeById) {
  ASSERT_DEATH({
    auto om = zlog::ObjectMap(0, {}, 0);
    om.stripe_by_id(0);
  }, "!stripes_by_id_.empty.+failed");

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(0, {}, 0);
    om.stripe_by_id(1);
  }, "!stripes_by_id_.empty.+failed");

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(0, {}, 0);
    om.stripe_by_id(2);
  }, "!stripes_by_id_.empty.+failed");

  {
    auto om = zlog::ObjectMap(1,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)}},
        0);
    om.stripe_by_id(0);
  }

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(1,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)}},
        0);
    om.stripe_by_id(1);
  }, "stripe_id <= it->second.max_stripe_id.+failed");

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(1,
        {{0, zlog::MultiStripe(0, 1, 1, 0, 1, 0)}},
        0);
    om.stripe_by_id(2);
  }, "stripe_id <= it->second.max_stripe_id.+failed");

  {
    auto om = zlog::ObjectMap(6,
        {{0, zlog::MultiStripe(0, 10, 10, 0, 1, 99)},
         {100, zlog::MultiStripe(1, 20, 30, 100, 2, 1299)},
         {1300, zlog::MultiStripe(3, 5, 6, 1300, 3, 1389)}},
        0);
    om.stripe_by_id(0);
    om.stripe_by_id(1);
    om.stripe_by_id(2);
    om.stripe_by_id(3);
    om.stripe_by_id(4);
    om.stripe_by_id(5);
  }

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(6,
        {{0, zlog::MultiStripe(0, 10, 10, 0, 1, 99)},
         {100, zlog::MultiStripe(1, 20, 30, 100, 2, 1299)},
         {1300, zlog::MultiStripe(3, 5, 6, 1300, 3, 1389)}},
        0);
    om.stripe_by_id(6);
  }, "stripe_id <= it->second.max_stripe_id.+failed");

  ASSERT_DEATH({
    auto om = zlog::ObjectMap(6,
        {{0, zlog::MultiStripe(0, 10, 10, 0, 1, 99)},
         {100, zlog::MultiStripe(1, 20, 30, 100, 2, 1299)},
         {1300, zlog::MultiStripe(3, 5, 6, 1300, 3, 1389)}},
        0);
    om.stripe_by_id(7);
  }, "stripe_id <= it->second.max_stripe_id.+failed");
}

TEST(ObjectMapDeathTest, MaxPos) {
  ASSERT_DEATH({
    auto om = zlog::ObjectMap(0, {}, 0);
    om.max_position();
  }, "stripe != stripes_by_pos_.crend.+failed");
}

TEST(ObjectMapDeathTest, ExpandMapping) {
  ASSERT_DEATH({
    zlog::Options options;
    options.stripe_slots = 0;
    auto om = zlog::ObjectMap(0, {}, 0);
    om.expand_mapping(0, options);
  }, "slots_ > 0.+failed");
}

TEST(ObjectMapTest, MapEmpty) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.next_stripe_id(), 0u);
  ASSERT_TRUE(om.empty());
  ASSERT_EQ(om.num_stripes(), 0u);

  ASSERT_FALSE(om.map(0).first);
  ASSERT_FALSE(om.map(1).first);
  ASSERT_FALSE(om.map(2).first);
}

TEST(ObjectMapTest, MapA) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        1,   // width
        1,   // slots
        0,   // min position
        1,   // instances
        0)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.next_stripe_id(), 1u);
  ASSERT_EQ(om.max_position(), 0u);
  ASSERT_FALSE(om.empty());
  ASSERT_EQ(om.num_stripes(), 1u);

  ASSERT_TRUE(om.map(0).first);
  ASSERT_TRUE(om.map(0).second);
  ASSERT_EQ(*om.map(0).first, "0.0");
  ASSERT_FALSE(om.map(1).first);
  ASSERT_FALSE(om.map(2).first);
}

TEST(ObjectMapTest, MapB) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        20,   // slots
        0,   // min position
        1,   // instances
        199)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_FALSE(om.empty());
  ASSERT_EQ(om.max_position(), 199u);
  ASSERT_EQ(om.num_stripes(), 1u);

  for (uint64_t p = 0; p < 200; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_TRUE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(111).first, "0.1");
  ASSERT_FALSE(om.map(200).first);
  ASSERT_FALSE(om.map(201).first);
}

TEST(ObjectMapTest, MapC) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        20,   // slots
        0,   // min position
        3,   // instances
        599)); // max position
  auto om = zlog::ObjectMap(3, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.next_stripe_id(), 3u);
  ASSERT_FALSE(om.empty());
  ASSERT_EQ(om.num_stripes(), 3u);

  for (uint64_t p = 0; p < 200; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(111).first, "0.1");
  for (uint64_t p = 200; p < 400; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(312).first, "1.2");
  for (uint64_t p = 400; p < 600; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_TRUE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(412).first, "2.2");
  ASSERT_FALSE(om.map(600).first);
  ASSERT_FALSE(om.map(601).first);
}

TEST(ObjectMapTest, MapD) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        10,   // slots
        0,   // min position
        1,   // instances
        99)); // max position
  stripes.emplace(100, zlog::MultiStripe(
        1,   // base id
        20,   // width
        30,   // slots
        100,   // min position
        2,   // instances
        1299)); // max position
  stripes.emplace(1300, zlog::MultiStripe(
        3,   // base id
        5,   // width
        6,   // slots
        1300,   // min position
        3,   // instances
        1389)); // max position
  auto om = zlog::ObjectMap(6, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.next_stripe_id(), 6u);
  ASSERT_FALSE(om.empty());
  ASSERT_EQ(om.num_stripes(), 6u);
  ASSERT_EQ(om.max_position(), 1389u);

  for (uint64_t p = 0; p < 100; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(75).first, "0.5");

  for (uint64_t p = 100; p < 700; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(105).first, "1.5");
  ASSERT_EQ(*om.map(698).first, "1.18");
  ASSERT_EQ(*om.map(699).first, "1.19");

  for (uint64_t p = 700; p < 1300; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(709).first, "2.9");
  ASSERT_EQ(*om.map(1297).first, "2.17");
  ASSERT_EQ(*om.map(1299).first, "2.19");

  for (uint64_t p = 1300; p < 1330; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(1300).first, "3.0");
  ASSERT_EQ(*om.map(1327).first, "3.2");
  ASSERT_EQ(*om.map(1329).first, "3.4");

  for (uint64_t p = 1330; p < 1360; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_FALSE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(1330).first, "4.0");
  ASSERT_EQ(*om.map(1331).first, "4.1");
  ASSERT_EQ(*om.map(1332).first, "4.2");
  ASSERT_EQ(*om.map(1359).first, "4.4");

  for (uint64_t p = 1360; p < 1390; p++) {
    ASSERT_TRUE(om.map(p).first);
    ASSERT_TRUE(om.map(p).second);
  }
  ASSERT_EQ(*om.map(1360).first, "5.0");
  ASSERT_EQ(*om.map(1377).first, "5.2");
  ASSERT_EQ(*om.map(1389).first, "5.4");

  ASSERT_FALSE(om.map(1390).first);
  ASSERT_FALSE(om.map(1391).first);
  ASSERT_FALSE(om.map(1392).first);
}

TEST(ObjectMapTest, ExpandMappingFromEmptyA) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_TRUE(om.empty());

  zlog::Options options;
  options.stripe_width = 33;
  options.stripe_slots = 7;

  auto maybe_om = om.expand_mapping(0, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.num_stripes(), 1u);

  auto stripe = om.stripe_by_id(0);
  ASSERT_EQ(stripe.width(), 33u);
  ASSERT_EQ(stripe.max_position(), 230u);

  maybe_om = om.expand_mapping(231, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.num_stripes(), 2u);

  stripe = om.stripe_by_id(1);
  ASSERT_EQ(stripe.width(), 33u);
  ASSERT_EQ(stripe.max_position(), 461u);
}

TEST(ObjectMapTest, ExpandMappingFromEmptyB) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_TRUE(om.empty());

  zlog::Options options;
  options.stripe_width = 97;
  options.stripe_slots = 17;

  auto maybe_om = om.expand_mapping(4940, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.num_stripes(), 3u);
  ASSERT_EQ(om.max_position(), 4946u);

  auto stripe = om.stripe_by_id(0);
  ASSERT_EQ(stripe.width(), 97u);
  ASSERT_EQ(stripe.max_position(), 1648u);

  maybe_om = om.expand_mapping(6595, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.num_stripes(), 4u);
  ASSERT_EQ(om.max_position(), 6595u);

  stripe = om.stripe_by_id(3);
  ASSERT_EQ(stripe.width(), 97u);
  ASSERT_EQ(stripe.max_position(), 6595u);
}

TEST(ObjectMapTest, ExpandMapping) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        10,   // slots
        0,   // min position
        1,   // instances
        99)); // max position
  stripes.emplace(100, zlog::MultiStripe(
        1,   // base id
        20,   // width
        30,   // slots
        100,   // min position
        2,   // instances
        1299)); // max position
  stripes.emplace(1300, zlog::MultiStripe(
        3,   // base id
        5,   // width
        6,   // slots
        1300,   // min position
        3,   // instances
        1389)); // max position
  auto om = zlog::ObjectMap(6, stripes, 0);
  ASSERT_TRUE(om.valid());

  zlog::Options options;
  for (uint64_t p = 0; p < 1390; p++) {
    ASSERT_FALSE(om.expand_mapping(p, options));
  }

  auto maybe_om = om.expand_mapping(1390, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());

  for (uint64_t p = 1390; p < 1420; p++) {
    ASSERT_FALSE(om.expand_mapping(p, options));
  }

  maybe_om = om.expand_mapping(1430, options);
  ASSERT_TRUE(maybe_om);
  om = *maybe_om;
  ASSERT_TRUE(om.valid());

  for (uint64_t p = 1420; p < 1450; p++) {
    ASSERT_FALSE(om.expand_mapping(p, options));
  }

  for (uint64_t p = 0; p < 1450; p++) {
    ASSERT_FALSE(om.expand_mapping(p, options));
    ASSERT_TRUE(om.map(p).first);
  }
  ASSERT_FALSE(om.map(1450).first);
}

TEST(ObjectMapTest, AdvanceMinPosition) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        20,   // slots
        0,   // min position
        1,   // instances
        199)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_EQ(om.min_valid_position(), 0u);

  auto maybe_om = om.advance_min_valid_position(0);
  ASSERT_FALSE(maybe_om);
  ASSERT_EQ(om.min_valid_position(), 0u);

  maybe_om = om.advance_min_valid_position(33);
  ASSERT_TRUE(maybe_om);
  ASSERT_EQ(om.min_valid_position(), 0u);
  om = *maybe_om;
  ASSERT_EQ(om.min_valid_position(), 33u);

  for (uint64_t p = 0; p <= 33; p++) {
    auto maybe_om = om.advance_min_valid_position(p);
    ASSERT_FALSE(maybe_om);
  }

  maybe_om = om.advance_min_valid_position(34);
  ASSERT_TRUE(maybe_om);
  ASSERT_EQ(om.min_valid_position(), 33u);
  om = *maybe_om;
  ASSERT_EQ(om.min_valid_position(), 34u);
}

// generates a range of starting states, then validates the new object map after
// applying operations like expand_mapping
TEST(ObjectMapTest, Range) {
  // build the initial stripes state for object map
  for (uint32_t width = 1; width < 10; width++) {
  for (uint32_t slots = 1; slots < 10; slots++) {
  for (uint64_t instances = 1; instances < 10; instances++) {
  for (int extra_stripes = 0; extra_stripes < 5; extra_stripes++) {

    uint64_t base_id = 0;
    uint64_t min_position = 0;

    std::map<uint64_t, zlog::MultiStripe> stripes;

    // first multistripe
    auto res = stripes.emplace(min_position,
        zlog::MultiStripe(base_id, width, slots, min_position,
          instances, (min_position + instances * width * slots - 1)));

    base_id += instances;
    min_position = res.first->second.max_position() + 1;
    uint64_t next_stripe_id = instances;

    // add more?
    for (int xx = 1; xx <= extra_stripes; xx++) {
      auto instances_tmp = instances * xx;
      auto width_tmp = width * xx;
      auto slots_tmp = slots * xx;

      res = stripes.emplace(min_position,
          zlog::MultiStripe(base_id, width_tmp, slots_tmp, min_position,
            instances_tmp, (min_position + instances_tmp * width_tmp * slots_tmp - 1)));

      base_id += instances_tmp;
      min_position = res.first->second.max_position() + 1;
      next_stripe_id += instances_tmp;
    }

    // build the object map with the set of starting multi stripes
    auto om = zlog::ObjectMap(next_stripe_id, stripes, 0);
    ASSERT_TRUE(om.valid());

    zlog::Options options;
    auto max_pos = om.max_position();
    for (auto expand_to = max_pos - 50; expand_to <= max_pos; expand_to++) {
      auto maybe_om = om.expand_mapping(expand_to, options);
      ASSERT_FALSE(maybe_om);
    }
    ASSERT_EQ(om.max_position(), max_pos);

    auto maybe_om = om.expand_mapping(max_pos+1, options);
    ASSERT_TRUE(maybe_om);
    om = *maybe_om;
    ASSERT_TRUE(om.valid());
    ASSERT_NE(om.max_position(), max_pos);

    maybe_om = om.expand_mapping(om.max_position()+50, options);
    ASSERT_TRUE(maybe_om);
    om = *maybe_om;
    ASSERT_TRUE(om.valid());

    maybe_om = om.advance_min_valid_position(om.min_valid_position()+1);
    ASSERT_TRUE(maybe_om);
    om = *maybe_om;
    ASSERT_TRUE(om.valid());
  }
  }
  }
  }
}

TEST(ObjectMapTest, StripeByIdA) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        1,   // width
        1,   // slots
        0,   // min position
        1,   // instances
        0)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());

  ASSERT_EQ(om.stripe_by_id(0),
      zlog::Stripe(0, 1, 0, 0));
}

TEST(ObjectMapTest, StripeByIdB) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        10,   // slots
        0,   // min position
        1,   // instances
        99)); // max position
  stripes.emplace(100, zlog::MultiStripe(
        1,   // base id
        20,   // width
        30,   // slots
        100,   // min position
        2,   // instances
        1299)); // max position
  stripes.emplace(1300, zlog::MultiStripe(
        3,   // base id
        5,   // width
        6,   // slots
        1300,   // min position
        3,   // instances
        1389)); // max position
  auto om = zlog::ObjectMap(6, stripes, 0);
  ASSERT_TRUE(om.valid());

  ASSERT_EQ(om.stripe_by_id(0),
      zlog::Stripe(0, 10, 0, 99));

  ASSERT_EQ(om.stripe_by_id(1),
      zlog::Stripe(1, 20, 100, 699));

  ASSERT_EQ(om.stripe_by_id(2),
      zlog::Stripe(2, 20, 700, 1299));

  ASSERT_EQ(om.stripe_by_id(3),
      zlog::Stripe(3, 5, 1300, 1329));

  ASSERT_EQ(om.stripe_by_id(4),
      zlog::Stripe(4, 5, 1330, 1359));

  ASSERT_EQ(om.stripe_by_id(5),
      zlog::Stripe(5, 5, 1360, 1389));
}

TEST(ObjectMapTest, MapStripeA) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        1,   // width
        1,   // slots
        0,   // min position
        1,   // instances
        0)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());

  ASSERT_TRUE(om.map_stripe(0));
  ASSERT_EQ(*om.map_stripe(0), zlog::Stripe(0, 1, 0, 0));

  ASSERT_FALSE(om.map_stripe(1));
}

TEST(ObjectMapTest, MapStripeB) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        10,   // slots
        0,   // min position
        1,   // instances
        99)); // max position
  stripes.emplace(100, zlog::MultiStripe(
        1,   // base id
        20,   // width
        30,   // slots
        100,   // min position
        2,   // instances
        1299)); // max position
  stripes.emplace(1300, zlog::MultiStripe(
        3,   // base id
        5,   // width
        6,   // slots
        1300,   // min position
        3,   // instances
        1389)); // max position
  auto om = zlog::ObjectMap(6, stripes, 0);
  ASSERT_TRUE(om.valid());

  for (uint64_t p = 0; p < 100; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(0, 10, 0, 99));
  }

  for (uint64_t p = 100; p < 700; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(1, 20, 100, 699));
  }

  for (uint64_t p = 700; p < 1300; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(2, 20, 700, 1299));
  }

  for (uint64_t p = 1300; p < 1330; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(3, 5, 1300, 1329));
  }

  for (uint64_t p = 1330; p < 1360; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(4, 5, 1330, 1359));
  }

  for (uint64_t p = 1360; p < 1390; p++) {
    ASSERT_TRUE(om.map_stripe(p));
    ASSERT_EQ(*om.map_stripe(p), zlog::Stripe(5, 5, 1360, 1389));
  }
}

TEST(ObjectMapTest, MapToEmpty) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(0, stripe_id, done);
    ASSERT_FALSE(objs);
    ASSERT_FALSE(done);
  }
}

TEST(ObjectMapTest, MapToSmall) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        1,   // width
        1,   // slots
        0,   // min position
        1,   // instances
        0)); // max position
  auto om = zlog::ObjectMap(1, stripes, 0);
  ASSERT_TRUE(om.valid());

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", true),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_TRUE(done);
    ASSERT_TRUE(objs->empty());
  }
}

TEST(ObjectMapTest, MapTo) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe(
        0,   // base id
        10,   // width
        10,   // slots
        0,   // min position
        1,   // instances
        99)); // max position
  stripes.emplace(100, zlog::MultiStripe(
        1,   // base id
        20,   // width
        30,   // slots
        100,   // min position
        2,   // instances
        1299)); // max position
  stripes.emplace(1300, zlog::MultiStripe(
        3,   // base id
        5,   // width
        6,   // slots
        1300,   // min position
        3,   // instances
        1389)); // max position
  auto om = zlog::ObjectMap(6, stripes, 0);
  ASSERT_TRUE(om.valid());

  for (uint64_t p = 0; p < 1390; p++) {
    bool done = false;
    uint64_t stripe_id = 0;

    auto objs = om.map_to(p, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
  }

  for (uint64_t p = 1390; p < 1400; p++) {
    bool done = false;
    uint64_t stripe_id = 0;

    auto objs = om.map_to(p, stripe_id, done);
    ASSERT_FALSE(objs);
    ASSERT_FALSE(done);
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;

    auto objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);

    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", false)
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_EQ(stripe_id, 2u);
    ASSERT_TRUE(objs->empty());

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_EQ(stripe_id, 3u);
    ASSERT_TRUE(objs->empty());

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_EQ(stripe_id, 4u);
    ASSERT_TRUE(objs->empty());

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_EQ(stripe_id, 5u);
    ASSERT_TRUE(objs->empty());

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_EQ(stripe_id, 6u);
    ASSERT_TRUE(objs->empty());

    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_TRUE(done);
    ASSERT_TRUE(objs->empty());

    done = false;
    stripe_id = 10;
    objs = om.map_to(0, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_TRUE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(1, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", false),
      std::make_pair("0.1", false)
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(1, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(9, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", false),
      std::make_pair("0.1", false),
      std::make_pair("0.2", false),
      std::make_pair("0.3", false),
      std::make_pair("0.4", false),
      std::make_pair("0.5", false),
      std::make_pair("0.6", false),
      std::make_pair("0.7", false),
      std::make_pair("0.8", false),
      std::make_pair("0.9", false),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(9, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(10, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", false),
      std::make_pair("0.1", false),
      std::make_pair("0.2", false),
      std::make_pair("0.3", false),
      std::make_pair("0.4", false),
      std::make_pair("0.5", false),
      std::make_pair("0.6", false),
      std::make_pair("0.7", false),
      std::make_pair("0.8", false),
      std::make_pair("0.9", false),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(10, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(47, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", false),
      std::make_pair("0.1", false),
      std::make_pair("0.2", false),
      std::make_pair("0.3", false),
      std::make_pair("0.4", false),
      std::make_pair("0.5", false),
      std::make_pair("0.6", false),
      std::make_pair("0.7", false),
      std::make_pair("0.8", false),
      std::make_pair("0.9", false),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(47, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(90, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", true),
      std::make_pair("0.1", false),
      std::make_pair("0.2", false),
      std::make_pair("0.3", false),
      std::make_pair("0.4", false),
      std::make_pair("0.5", false),
      std::make_pair("0.6", false),
      std::make_pair("0.7", false),
      std::make_pair("0.8", false),
      std::make_pair("0.9", false),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(90, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(95, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", true),
      std::make_pair("0.1", true),
      std::make_pair("0.2", true),
      std::make_pair("0.3", true),
      std::make_pair("0.4", true),
      std::make_pair("0.5", true),
      std::make_pair("0.6", false),
      std::make_pair("0.7", false),
      std::make_pair("0.8", false),
      std::make_pair("0.9", false),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(95, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(99, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected{
      std::make_pair("0.0", true),
      std::make_pair("0.1", true),
      std::make_pair("0.2", true),
      std::make_pair("0.3", true),
      std::make_pair("0.4", true),
      std::make_pair("0.5", true),
      std::make_pair("0.6", true),
      std::make_pair("0.7", true),
      std::make_pair("0.8", true),
      std::make_pair("0.9", true),
    };
    ASSERT_EQ(*objs, expected);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(99, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    ASSERT_TRUE(objs->empty());
  }

  {
    bool done = false;
    uint64_t stripe_id = 0;
    auto objs = om.map_to(100, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected0{
      std::make_pair("0.0", true),
      std::make_pair("0.1", true),
      std::make_pair("0.2", true),
      std::make_pair("0.3", true),
      std::make_pair("0.4", true),
      std::make_pair("0.5", true),
      std::make_pair("0.6", true),
      std::make_pair("0.7", true),
      std::make_pair("0.8", true),
      std::make_pair("0.9", true),
    };
    ASSERT_EQ(*objs, expected0);
    ASSERT_EQ(stripe_id, 1u);
    ASSERT_FALSE(done);

    objs = om.map_to(100, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected1{
      std::make_pair("1.0", false),
    };
    ASSERT_EQ(*objs, expected1);
    ASSERT_EQ(stripe_id, 2u);
  }

  {
    bool done = false;
    uint64_t stripe_id = 2;
    auto objs = om.map_to(1298, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected0{
      std::make_pair("2.0", true),
      std::make_pair("2.1", true),
      std::make_pair("2.2", true),
      std::make_pair("2.3", true),
      std::make_pair("2.4", true),
      std::make_pair("2.5", true),
      std::make_pair("2.6", true),
      std::make_pair("2.7", true),
      std::make_pair("2.8", true),
      std::make_pair("2.9", true),
      std::make_pair("2.10", true),
      std::make_pair("2.11", true),
      std::make_pair("2.12", true),
      std::make_pair("2.13", true),
      std::make_pair("2.14", true),
      std::make_pair("2.15", true),
      std::make_pair("2.16", true),
      std::make_pair("2.17", true),
      std::make_pair("2.18", true),
      std::make_pair("2.19", false),
    };
    ASSERT_EQ(*objs, expected0);
    ASSERT_EQ(stripe_id, 3u);
    ASSERT_FALSE(done);
  }

  {
    bool done = false;
    uint64_t stripe_id = 2;
    auto objs = om.map_to(1301, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected0{
      std::make_pair("2.0", true),
      std::make_pair("2.1", true),
      std::make_pair("2.2", true),
      std::make_pair("2.3", true),
      std::make_pair("2.4", true),
      std::make_pair("2.5", true),
      std::make_pair("2.6", true),
      std::make_pair("2.7", true),
      std::make_pair("2.8", true),
      std::make_pair("2.9", true),
      std::make_pair("2.10", true),
      std::make_pair("2.11", true),
      std::make_pair("2.12", true),
      std::make_pair("2.13", true),
      std::make_pair("2.14", true),
      std::make_pair("2.15", true),
      std::make_pair("2.16", true),
      std::make_pair("2.17", true),
      std::make_pair("2.18", true),
      std::make_pair("2.19", true),
    };
    ASSERT_EQ(*objs, expected0);
    ASSERT_EQ(stripe_id, 3u);
    ASSERT_FALSE(done);

    objs = om.map_to(1301, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected1{
      std::make_pair("3.0", false),
      std::make_pair("3.1", false),
    };
    ASSERT_EQ(*objs, expected1);
    ASSERT_EQ(stripe_id, 4u);
  }

  {
    bool done = false;
    uint64_t stripe_id = 2;
    auto objs = om.map_to(1388, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected0{
      std::make_pair("2.0", true),
      std::make_pair("2.1", true),
      std::make_pair("2.2", true),
      std::make_pair("2.3", true),
      std::make_pair("2.4", true),
      std::make_pair("2.5", true),
      std::make_pair("2.6", true),
      std::make_pair("2.7", true),
      std::make_pair("2.8", true),
      std::make_pair("2.9", true),
      std::make_pair("2.10", true),
      std::make_pair("2.11", true),
      std::make_pair("2.12", true),
      std::make_pair("2.13", true),
      std::make_pair("2.14", true),
      std::make_pair("2.15", true),
      std::make_pair("2.16", true),
      std::make_pair("2.17", true),
      std::make_pair("2.18", true),
      std::make_pair("2.19", true),
    };
    ASSERT_EQ(*objs, expected0);
    ASSERT_EQ(stripe_id, 3u);
    ASSERT_FALSE(done);

    stripe_id = 5;
    objs = om.map_to(1388, stripe_id, done);
    ASSERT_TRUE(objs);
    ASSERT_FALSE(done);
    std::vector<std::pair<std::string, bool>> expected1{
      std::make_pair("5.0", true),
      std::make_pair("5.1", true),
      std::make_pair("5.2", true),
      std::make_pair("5.3", true),
      std::make_pair("5.4", false),
    };
    ASSERT_EQ(*objs, expected1);
    ASSERT_EQ(stripe_id, 6u);
  }
}
