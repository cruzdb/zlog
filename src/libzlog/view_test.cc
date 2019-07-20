#include "gtest/gtest.h"
#include "include/zlog/options.h"
#include "libzlog/view.h"

#if 0
  std::map<uint64_t, zlog::MultiStripe> stripes;
  stripes.emplace(0, zlog::MultiStripe("p",
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
#endif

TEST(ViewTest, ExpandMapping) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_TRUE(om.empty());

  zlog::SequencerConfig seqconf(22, "asdf", 33);
  zlog::View view(om, seqconf);
  ASSERT_TRUE(view.object_map().empty());
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);

  zlog::Options options;
  options.stripe_width = 11;
  options.stripe_slots = 20;

  auto maybe_view = view.expand_mapping(0, options);
  ASSERT_TRUE(maybe_view);
  view = *maybe_view;
  ASSERT_EQ(view.object_map().num_stripes(), 1u);
  ASSERT_EQ(view.object_map().stripe_by_id(0).width(), 11u);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);

  maybe_view = view.expand_mapping(230, options);
  ASSERT_TRUE(maybe_view);
  view = *maybe_view;
  ASSERT_EQ(view.object_map().num_stripes(), 2u);
  ASSERT_EQ(view.object_map().stripe_by_id(0).width(), 11u);
  ASSERT_EQ(view.object_map().stripe_by_id(1).width(), 11u);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);

  maybe_view = view.expand_mapping(0, options);
  ASSERT_FALSE(maybe_view);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
  maybe_view = view.expand_mapping(219, options);
  ASSERT_FALSE(maybe_view);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
  maybe_view = view.expand_mapping(220, options);
  ASSERT_FALSE(maybe_view);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
  maybe_view = view.expand_mapping(250, options);
  ASSERT_FALSE(maybe_view);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
}

TEST(ViewTest, AdvanceMinValidPosition) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_TRUE(om.empty());

  zlog::SequencerConfig seqconf(22, "asdf", 33);
  zlog::View view(om, seqconf);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
  ASSERT_EQ(view.object_map(), om);

  auto maybe_view = view.advance_min_valid_position(0);
  ASSERT_FALSE(maybe_view);
  ASSERT_EQ(*view.seq_config(), seqconf);
  ASSERT_EQ(view.object_map(), om);

  maybe_view = view.advance_min_valid_position(10);
  ASSERT_TRUE(maybe_view);
  view = *maybe_view;
  ASSERT_EQ(view.object_map(), zlog::ObjectMap(0, stripes, 10));
  ASSERT_EQ(view.object_map().min_valid_position(), 10u);
  ASSERT_EQ(*view.seq_config(), seqconf);

  maybe_view = view.advance_min_valid_position(7);
  ASSERT_FALSE(maybe_view);
  maybe_view = view.advance_min_valid_position(10);
  ASSERT_FALSE(maybe_view);

  maybe_view = view.advance_min_valid_position(11);
  ASSERT_TRUE(maybe_view);
  view = *maybe_view;
  ASSERT_EQ(view.object_map(), zlog::ObjectMap(0, stripes, 11));
  ASSERT_EQ(view.object_map().min_valid_position(), 11u);
  ASSERT_EQ(*view.seq_config(), seqconf);
}

TEST(ViewTest, SetSequencerConfig) {
  std::map<uint64_t, zlog::MultiStripe> stripes;
  auto om = zlog::ObjectMap(0, stripes, 0);
  ASSERT_TRUE(om.valid());
  ASSERT_TRUE(om.empty());

  zlog::View view(om, boost::none);
  ASSERT_FALSE(view.seq_config());
  ASSERT_EQ(view.object_map(), om);

  zlog::SequencerConfig seqconf(22, "asdf", 33);
  view = view.set_sequencer_config(seqconf);
  ASSERT_TRUE(view.seq_config());
  ASSERT_EQ(*view.seq_config(), seqconf);
  ASSERT_EQ(view.object_map(), om);
}
