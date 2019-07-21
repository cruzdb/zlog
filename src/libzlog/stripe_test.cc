#include "gtest/gtest.h"
#include "libzlog/stripe.h"

TEST(StripeDeathTest, Constructor) {
  // width == 0
  ASSERT_DEATH({
    zlog::Stripe(0, 0, 0, 0);
  }, "width_ > 0.+failed");

  // stripe id > 0 -> min pos > 0
  ASSERT_DEATH({
    zlog::Stripe(1, 1, 0, 0);
  }, "min_position_ > 0.+failed");

  // stripe id == 0 -> min pos == 0
  ASSERT_DEATH({
    zlog::Stripe(0, 1, 1, 0);
  }, "min_position_ == 0.+failed");

  // min pos > max pos
  ASSERT_DEATH({
    zlog::Stripe(1, 1, 1, 0);
  }, "min_position_ <= max_position_.+failed");

  // max pos isn't at least `width` larger than min pos
  ASSERT_DEATH({
    zlog::Stripe(0, 10, 0, 0);
  }, "max_position_ >= \\(min_position_ \\+ width_ - 1\\).+failed");
  ASSERT_DEATH({
    zlog::Stripe(1, 10, 8, 12);
  }, "max_position_ >= \\(min_position_ \\+ width_ - 1\\).+failed");

  // max pos is big enough, but isn't a multiple of width
  ASSERT_DEATH({
    zlog::Stripe(0, 10, 0, 10);
  }, "\\(max_position_ - min_position_ \\+ 1\\) % width_ == 0.+failed");
  ASSERT_DEATH({
    zlog::Stripe(1, 10, 7, 19);
  }, "\\(max_position_ - min_position_ \\+ 1\\) % width_ == 0.+failed");
}

TEST(StripeTest, Basic) {
  auto s = zlog::Stripe(0, 1, 0, 3);
  ASSERT_EQ(s.width(), 1u);
  ASSERT_EQ(s.min_position(), 0u);
  ASSERT_EQ(s.max_position(), 3u);
  ASSERT_EQ(s.oids(), std::vector<std::string>{"0.0"});

  s = zlog::Stripe(1, 2, 3, 4);
  ASSERT_EQ(s.width(), 2u);
  ASSERT_EQ(s.min_position(), 3u);
  ASSERT_EQ(s.max_position(), 4u);
  ASSERT_EQ(s.oids(), std::vector<std::string>({"1.0","1.1"}));

  s = zlog::Stripe(6, 3, 4, 9);
  ASSERT_EQ(s.width(), 3u);
  ASSERT_EQ(s.min_position(), 4u);
  ASSERT_EQ(s.max_position(), 9u);
  ASSERT_EQ(s.oids(), std::vector<std::string>({"6.0", "6.1", "6.2"}));
}

TEST(StripeTest, MakeOID) {
  ASSERT_EQ(
      zlog::Stripe::make_oid(33, 44, 101),
      "33.13");
}

TEST(StripeTest, Equality) {
  ASSERT_TRUE(
      zlog::Stripe(1, 1, 1, 1) ==
      zlog::Stripe(1, 1, 1, 1));
  ASSERT_TRUE(
      zlog::Stripe(1, 1, 1, 3) ==
      zlog::Stripe(1, 1, 1, 3));
  ASSERT_TRUE(
      zlog::Stripe(1, 1, 2, 3) ==
      zlog::Stripe(1, 1, 2, 3));
  ASSERT_TRUE(
      zlog::Stripe(1, 2, 2, 3) ==
      zlog::Stripe(1, 2, 2, 3));
  ASSERT_TRUE(
      zlog::Stripe(2, 2, 2, 3) ==
      zlog::Stripe(2, 2, 2, 3));

  ASSERT_FALSE(
      zlog::Stripe(1, 1, 1, 1) !=
      zlog::Stripe(1, 1, 1, 1));
  ASSERT_TRUE(
      zlog::Stripe(1, 1, 1, 3) !=
      zlog::Stripe(2, 1, 1, 3));
  ASSERT_TRUE(
      zlog::Stripe(1, 1, 2, 3) !=
      zlog::Stripe(1, 2, 2, 3));
  ASSERT_TRUE(
      zlog::Stripe(1, 2, 2, 5) !=
      zlog::Stripe(1, 2, 4, 5));
  ASSERT_TRUE(
      zlog::Stripe(2, 2, 2, 3) !=
      zlog::Stripe(2, 2, 2, 5));
}

TEST(StripeTest, Range) {
  for (uint64_t stripe_id = 0; stripe_id < 10; stripe_id++) {
    for (uint32_t width = 1; width < 10; width++) {
      for (uint32_t slots = 1; slots < 10; slots++) {
        for (uint64_t min_position = 0; min_position < 10; min_position++) {

          // basic assumption about how stripes are built. not necessarily
          // fundamental and might change in the future.
          if (stripe_id == 0 && min_position > 0) {
            continue;
          } else if (stripe_id > 0 && min_position == 0) {
            continue;
          }

          zlog::Stripe(stripe_id, width, min_position,
              (min_position + width * slots - 1));
        }
      }
    }
  }
}

TEST(MultiStripeDeathTest, Constructor) {
  // width == 0
  ASSERT_DEATH({
    zlog::MultiStripe(0, 0, 1, 0, 1, 0);
  }, "width_ > 0.+failed");

  // slots == 0
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 0, 0, 1, 0);
  }, "slots_ > 0.+failed");

  // instances == 0
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 0, 0, 0);
  }, "instances_ > 0.+failed");

  // base_id > 0 -> min_pos > 0
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 0, 1, 1);
  }, "min_position_ > 0.+failed");

  // base_id == 0 -> min_pos == 0
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 1, 1, 1);
  }, "min_position_ == 0.+failed");

  // min pos > max pos
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 1, 0);
  }, "min_position_ <= max_position_.+failed");

  // test max pos: base id = 0
  {
    auto x =
    zlog::MultiStripe(0, 1, 1, 0, 1, 0);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 0, 1, 1);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 0, 1, 2);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");


  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 0, 2, 0);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  {
    auto x =
    zlog::MultiStripe(0, 1, 1, 0, 2, 1);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(0, 1, 1, 0, 2, 2);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");


  ASSERT_DEATH({
    zlog::MultiStripe(0, 2, 3, 0, 2, 0);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(0, 2, 3, 0, 2, 1);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(0, 2, 3, 0, 2, 2);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  {
    auto x =
    zlog::MultiStripe(0, 2, 3, 0, 2, 11);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(0, 2, 3, 0, 2, 12);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(0, 2, 3, 0, 2, 13);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");

  // test max pos: base id = 1
  {
    auto x =
    zlog::MultiStripe(1, 1, 1, 1, 1, 1);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 1, 2);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 1, 3);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");


  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 2, 1);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  {
    auto x =
    zlog::MultiStripe(1, 1, 1, 1, 2, 2);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 2, 3);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");


  ASSERT_DEATH({
    zlog::MultiStripe(1, 2, 3, 1, 2, 1);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(1, 2, 3, 1, 2, 2);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  {
    auto x =
    zlog::MultiStripe(1, 2, 3, 1, 2, 12);
    (void)x;
  }
  ASSERT_DEATH({
    zlog::MultiStripe(1, 2, 3, 1, 2, 13);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
  ASSERT_DEATH({
    zlog::MultiStripe(1, 2, 3, 1, 2, 14);
  }, "max_position_ == \\(min_position_ \\+ \\(instances_ \\* width_ \\* slots_\\) - 1\\)");
}

TEST(MultiStripeDeathTest, Map) {
  // stripe id < base_id
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 1, 1).map(0, 0);
  }, "base_id_ <= stripe_id.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 2, 2).map(0, 0);
  }, "base_id_ <= stripe_id.+failed");

  // stripe id > max stripe id
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 1, 1).map(2, 0);
  }, "stripe_id <= max_stripe_id.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe(1, 1, 1, 1, 2, 2).map(3, 0);
  }, "stripe_id <= max_stripe_id.+failed");

  // pos < min pos
  ASSERT_DEATH({
    zlog::MultiStripe(10, 10, 10, 1000, 1, 1099).map(10, 99);
  }, "min_position_ <= position.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe(10, 10, 10, 1000, 2, 1199).map(10, 99);
  }, "min_position_ <= position.+failed");

  // pos > max pos
  ASSERT_DEATH({
    zlog::MultiStripe(10, 10, 10, 1000, 1, 1099).map(10, 1111);
  }, "position <= max_position_.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe(10, 10, 10, 1000, 2, 1199).map(10, 2111);
  }, "position <= max_position_.+failed");
}

TEST(MultiStripeTest, Basic) {
  auto s = zlog::MultiStripe(0, 10, 20, 0, 1, 199);
  ASSERT_EQ(s.base_id(), 0u);
  ASSERT_EQ(s.max_stripe_id(), 0u);
  ASSERT_EQ(s.width(), 10u);
  ASSERT_EQ(s.slots(), 20u);
  ASSERT_EQ(s.min_position(), 0u);
  ASSERT_EQ(s.instances(), 1u);
  ASSERT_EQ(s.max_position(), 199u);

  s = zlog::MultiStripe(7, 10, 20, 10, 1, 209);
  ASSERT_EQ(s.base_id(), 7u);
  ASSERT_EQ(s.max_stripe_id(), 7u);
  ASSERT_EQ(s.width(), 10u);
  ASSERT_EQ(s.slots(), 20u);
  ASSERT_EQ(s.min_position(), 10u);
  ASSERT_EQ(s.instances(), 1u);
  ASSERT_EQ(s.max_position(), 209u);

  s = zlog::MultiStripe(7, 10, 20, 10, 3, 609);
  ASSERT_EQ(s.base_id(), 7u);
  ASSERT_EQ(s.max_stripe_id(), 9u);
  ASSERT_EQ(s.width(), 10u);
  ASSERT_EQ(s.slots(), 20u);
  ASSERT_EQ(s.min_position(), 10u);
  ASSERT_EQ(s.instances(), 3u);
  ASSERT_EQ(s.max_position(), 609u);
}

TEST(MultiStripeTest, Map) {
  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 1, 99).map(0, 0),
    "0.0");

  ASSERT_EQ(
    zlog::MultiStripe(10, 10, 10, 1000, 1, 1099).map(10, 1077),
    "10.7");

  ASSERT_EQ(
    zlog::MultiStripe(10, 10, 10, 1000, 2, 1199).map(11, 1077),
    "11.7");
}

TEST(MultiStripeTest, Extend) {
  ASSERT_NE(
    zlog::MultiStripe(0, 10, 10, 0, 1, 99).extend(),
    zlog::MultiStripe(0, 10, 10, 0, 1, 99));

  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 1, 99).extend(),
    zlog::MultiStripe(0, 10, 10, 0, 2, 199));
}

TEST(MultiStripeTest, StripeById) {
  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 1, 99).stripe_by_id(0),
    zlog::Stripe(0, 10, 0, 99));

  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 10, 999).stripe_by_id(0),
    zlog::Stripe(0, 10, 0, 99));
  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 10, 999).stripe_by_id(1),
    zlog::Stripe(1, 10, 100, 199));
  ASSERT_EQ(
    zlog::MultiStripe(0, 10, 10, 0, 10, 999).stripe_by_id(9),
    zlog::Stripe(9, 10, 900, 999));

  ASSERT_EQ(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(1),
    zlog::Stripe(1, 10, 100, 199));
  ASSERT_EQ(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(2),
    zlog::Stripe(2, 10, 200, 299));
  ASSERT_EQ(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(9),
    zlog::Stripe(9, 10, 900, 999));

  ASSERT_NE(
    zlog::MultiStripe(0, 10, 10, 0, 1, 99).stripe_by_id(0),
    zlog::Stripe(0, 20, 0, 99));
  ASSERT_NE(
    zlog::MultiStripe(0, 10, 10, 0, 10, 999).stripe_by_id(0),
    zlog::Stripe(0, 10, 0, 199));
  ASSERT_NE(
    zlog::MultiStripe(0, 10, 10, 0, 10, 999).stripe_by_id(1),
    zlog::Stripe(1, 10, 100, 299));

  ASSERT_NE(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(1),
    zlog::Stripe(2, 10, 100, 199));
  ASSERT_NE(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(2),
    zlog::Stripe(2, 10, 100, 299));
  ASSERT_NE(
    zlog::MultiStripe(1, 10, 10, 100, 10, 1099).stripe_by_id(2),
    zlog::Stripe(2, 10, 200, 399));
}

TEST(MultiStripeTest, Range) {
  for (uint64_t base_id = 0; base_id < 10; base_id++) {
    for (uint32_t width = 1; width < 10; width++) {
      for (uint32_t slots = 1; slots < 10; slots++) {
        for (uint64_t min_position = 0; min_position < 10; min_position++) {
          for (uint64_t instances = 1; instances < 10; instances++) {

            // basic assumption about how stripes are built. not necessarily
            // fundamental and might change in the future.
            if (base_id == 0 && min_position > 0) {
              continue;
            } else if (base_id > 0 && min_position == 0) {
              continue;
            }

            zlog::MultiStripe(base_id, width, slots, min_position, instances,
                (min_position + instances * width * slots - 1));
          }
        }
      }
    }
  }
}

TEST(MultiStripeTest, Equality) {
  ASSERT_TRUE(
      zlog::MultiStripe(0, 1, 1, 0, 1, 0) ==
      zlog::MultiStripe(0, 1, 1, 0, 1, 0));
  ASSERT_TRUE(
      zlog::MultiStripe(0, 1, 1, 0, 2, 1) ==
      zlog::MultiStripe(0, 1, 1, 0, 2, 1));
  ASSERT_TRUE(
      zlog::MultiStripe(0, 1, 2, 0, 2, 3) ==
      zlog::MultiStripe(0, 1, 2, 0, 2, 3));
  ASSERT_TRUE(
      zlog::MultiStripe(0, 3, 2, 0, 2, 11) ==
      zlog::MultiStripe(0, 3, 2, 0, 2, 11));

  ASSERT_TRUE(
      zlog::MultiStripe(1, 1, 1, 1, 1, 1) ==
      zlog::MultiStripe(1, 1, 1, 1, 1, 1));
  ASSERT_TRUE(
      zlog::MultiStripe(1, 1, 1, 1, 2, 2) ==
      zlog::MultiStripe(1, 1, 1, 1, 2, 2));
  ASSERT_TRUE(
      zlog::MultiStripe(1, 1, 2, 1, 2, 4) ==
      zlog::MultiStripe(1, 1, 2, 1, 2, 4));
  ASSERT_TRUE(
      zlog::MultiStripe(1, 3, 2, 1, 2, 12) ==
      zlog::MultiStripe(1, 3, 2, 1, 2, 12));

  ASSERT_FALSE(
      zlog::MultiStripe(0, 1, 1, 0, 1, 0) !=
      zlog::MultiStripe(0, 1, 1, 0, 1, 0));

  ASSERT_TRUE(
      zlog::MultiStripe(0, 1, 1, 0, 1, 0) !=
      zlog::MultiStripe(0, 1, 1, 0, 2, 1));
  ASSERT_TRUE(
      zlog::MultiStripe(0, 1, 3, 0, 2, 5) !=
      zlog::MultiStripe(0, 1, 2, 0, 2, 3));
  ASSERT_TRUE(
      zlog::MultiStripe(0, 4, 2, 0, 2, 15) !=
      zlog::MultiStripe(0, 3, 2, 0, 2, 11));

  ASSERT_TRUE(
      zlog::MultiStripe(1, 1, 1, 1, 1, 1) !=
      zlog::MultiStripe(1, 1, 1, 1, 2, 2));
  ASSERT_TRUE(
      zlog::MultiStripe(1, 1, 2, 1, 2, 4) !=
      zlog::MultiStripe(1, 1, 2, 1, 3, 6));
  ASSERT_TRUE(
      zlog::MultiStripe(1, 3, 2, 1, 2, 12) !=
      zlog::MultiStripe(1, 3, 2, 2, 2, 13));
}
