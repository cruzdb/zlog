#ifndef ZLOG_STRIPE_HISTORY_H_
#define ZLOG_STRIPE_HISTORY_H_
#include <map>
#include <rados/librados.hpp>

class StripeHistory {
 public:
  struct Stripe {
    uint64_t epoch;
    int width;
  };

  void AddStripe(uint64_t position, uint64_t epoch, int width);

  Stripe FindStripe(uint64_t position) const;
  Stripe LatestStripe() const;

  bool Empty() const;

  ceph::bufferlist Serialize() const;
  int Deserialize(ceph::bufferlist& bl);

 private:
  std::map<uint64_t, Stripe> history_;
};

#endif
