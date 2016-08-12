#ifndef ZLOG_STRIPE_HISTORY_H_
#define ZLOG_STRIPE_HISTORY_H_
#include <map>
#include "proto/zlog.pb.h"

class StripeHistory {
 public:
  struct Stripe {
    uint64_t epoch;
    int width;
  };

  void AddStripe(uint64_t position, uint64_t epoch, int width);
  void CloneLatestStripe(uint64_t position, uint64_t epoch);

  Stripe FindStripe(uint64_t position) const;
  Stripe LatestStripe(uint64_t *pos = NULL) const;

  bool Empty() const;

  zlog_proto::MetaLog Serialize() const;
  int Deserialize(const zlog_proto::MetaLog& data);

 private:
  std::map<uint64_t, Stripe> history_;
};

#endif
