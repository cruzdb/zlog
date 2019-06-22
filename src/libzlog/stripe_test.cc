#include "gtest/gtest.h"
#include "libzlog/stripe.h"

// Stripe TODO
//  - test private members
//  - equality operators
//
// MultiStripe
//  - encode/decode
//  - equality operators

TEST(StripeDeathTest, Constructor) {
  // empty prefix
  ASSERT_DEATH({
    zlog::Stripe("", 0, 1, 0, 0);
  }, "prefix.+failed");

  // width == 0
  ASSERT_DEATH({
    zlog::Stripe("p", 0, 0, 0, 0);
  }, "width.+failed");

  // min pos > max pos
  ASSERT_DEATH({
    zlog::Stripe("p", 0, 1, 1, 0);
  }, "min_pos.+max_pos.+failed");

  // stripe id > 0 -> positive min/max pos
  ASSERT_DEATH({
    zlog::Stripe("p", 1, 1, 0, 1);
  }, "min_pos.+failed");
  ASSERT_DEATH({
    zlog::Stripe("p", 1, 1, 1, 0);
  }, "max_pos.+failed");
}

TEST(StripeTest, Basic) {
  {
    auto s = zlog::Stripe("p", 0, 1, 2, 3);
    ASSERT_EQ(s.width(), 1u);
    ASSERT_EQ(s.min_position(), 2u);
    ASSERT_EQ(s.max_position(), 3u);
    ASSERT_EQ(s.oids(), std::vector<std::string>{"p.0.0"});
  }

  // allocate in new scope: Stripe doesn't define move assignment
  {
    auto s = zlog::Stripe("p", 0, 2, 3, 4);
    ASSERT_EQ(s.width(), 2u);
    ASSERT_EQ(s.min_position(), 3u);
    ASSERT_EQ(s.max_position(), 4u);
    ASSERT_EQ(s.oids(), std::vector<std::string>({"p.0.0","p.0.1"}));
  }

  {
    auto s = zlog::Stripe("p", 6, 3, 4, 5);
    ASSERT_EQ(s.width(), 3u);
    ASSERT_EQ(s.min_position(), 4u);
    ASSERT_EQ(s.max_position(), 5u);
    ASSERT_EQ(s.oids(), std::vector<std::string>({"p.6.0", "p.6.1", "p.6.2"}));
  }
}

TEST(StripeTest, MakeOID) {
  ASSERT_EQ(
      zlog::Stripe::make_oid("asdf", 33, 44, 101),
      "asdf.33.13");
}

TEST(MultiStripeDeathTest, Constructor) {
  // empty prefix
  ASSERT_DEATH({
    zlog::MultiStripe("", 0, 1, 1, 0, 1, 0);
  }, "prefix.+failed");

  // width == 0
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 0, 1, 0, 1, 0);
  }, "width.+failed");

  // slots == 0
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 0, 0, 1, 0);
  }, "slots.+failed");

  // instances == 0
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 1, 0, 0, 0);
  }, "instances.+failed");

  // min pos > max pos
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 1, 1, 1, 0);
  }, "min_pos.+max_pos.+failed");

  // base id > 0 -> positive min/max pos
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 0, 1, 1);
  }, "min_pos.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 1, 1, 0);
  }, "max_pos.+failed");

  // base id == 0, instances > 1 -> min pos >= 0, max pos > 0
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 1, 0, 2, 0);
  }, "max_pos.+failed");

  // max position is not valid
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 1, 10, 1, 10000);
  }, "max_position_.+min_position_.+instances_.+width_.+slots_.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 0, 1, 1, 10, 2, 10000);
  }, "max_position_.+min_position_.+instances_.+width_.+slots_.+failed");
}

TEST(MultiStripeDeathTest, Map) {
  // stripe id < base_id
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 1, 1, 1).map(0, 0);
  }, "base_id.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 1, 2, 1).map(0, 0);
  }, "base_id.+failed");

  // stripe id > max stripe id
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 1, 1, 1).map(2, 0);
  }, "max_stripe_id.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 1, 1, 1, 1, 2, 1).map(3, 0);
  }, "max_stripe_id.+failed");

  // pos < min pos
  ASSERT_DEATH({
    zlog::MultiStripe("p", 10, 10, 10, 1000, 1, 1099).map(10, 99);
  }, "min_position.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 10, 10, 10, 1000, 2, 1099).map(10, 99);
  }, "min_position.+failed");

  // pos > max pos
  ASSERT_DEATH({
    zlog::MultiStripe("p", 10, 10, 10, 1000, 1, 1099).map(10, 1111);
  }, "max_position.+failed");
  ASSERT_DEATH({
    zlog::MultiStripe("p", 10, 10, 10, 1000, 2, 1099).map(10, 1111);
  }, "max_position.+failed");
}

TEST(MultiStripeTest, Basic) {
  {
    auto s = zlog::MultiStripe("p", 0, 10, 20, 0, 1, 100);
    ASSERT_EQ(s.base_id(), 0u);
    ASSERT_EQ(s.max_stripe_id(), 0u);
    ASSERT_EQ(s.width(), 10u);
    ASSERT_EQ(s.slots(), 20u);
    ASSERT_EQ(s.min_position(), 0u);
    ASSERT_EQ(s.instances(), 1u);
    ASSERT_EQ(s.max_position(), 100u);
  }

  // allocate in new scope: MultiStripe doesn't define move assignment
  {
    auto s = zlog::MultiStripe("p", 7, 10, 20, 10, 1, 100);
    ASSERT_EQ(s.base_id(), 7u);
    ASSERT_EQ(s.max_stripe_id(), 7u);
    ASSERT_EQ(s.width(), 10u);
    ASSERT_EQ(s.slots(), 20u);
    ASSERT_EQ(s.min_position(), 10u);
    ASSERT_EQ(s.instances(), 1u);
    ASSERT_EQ(s.max_position(), 100u);
  }

  {
    auto s = zlog::MultiStripe("p", 7, 10, 20, 10, 3, 100);
    ASSERT_EQ(s.base_id(), 7u);
    ASSERT_EQ(s.max_stripe_id(), 9u);
    ASSERT_EQ(s.width(), 10u);
    ASSERT_EQ(s.slots(), 20u);
    ASSERT_EQ(s.min_position(), 10u);
    ASSERT_EQ(s.instances(), 3u);
    ASSERT_EQ(s.max_position(), 100u);
  }
}

TEST(MultiStripeTest, Map) {
  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99).map(0, 0),
    "p.0.0");

  ASSERT_EQ(
    zlog::MultiStripe("p", 10, 10, 10, 1000, 1, 1099).map(10, 1077),
    "p.10.7");

  ASSERT_EQ(
    zlog::MultiStripe("p", 10, 10, 10, 1000, 2, 1099).map(11, 1077),
    "p.11.7");
}

TEST(MultiStripeTest, Extend) {
  ASSERT_NE(
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99).extend(),
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99));

  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99).extend(),
    zlog::MultiStripe("p", 0, 10, 10, 0, 2, 199));
}

TEST(MultiStripeTest, StripeById) {
  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99).stripe_by_id(0),
    zlog::Stripe("p", 0, 10, 0, 99));

  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 10, 999).stripe_by_id(0),
    zlog::Stripe("p", 0, 10, 0, 99));
  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 10, 999).stripe_by_id(1),
    zlog::Stripe("p", 1, 10, 100, 199));
  ASSERT_EQ(
    zlog::MultiStripe("p", 0, 10, 10, 0, 10, 999).stripe_by_id(9),
    zlog::Stripe("p", 9, 10, 900, 999));

  ASSERT_NE(
    zlog::MultiStripe("p", 0, 10, 10, 0, 1, 99).stripe_by_id(0),
    zlog::Stripe("x", 0, 10, 0, 99));
  ASSERT_NE(
    zlog::MultiStripe("p", 0, 10, 10, 0, 10, 999).stripe_by_id(0),
    zlog::Stripe("p", 0, 10, 1, 99));
  ASSERT_NE(
    zlog::MultiStripe("p", 0, 10, 10, 0, 10, 999).stripe_by_id(1),
    zlog::Stripe("p", 1, 10, 100, 299));
}
