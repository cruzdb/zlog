#ifndef ZLOG_STRIPE_HISTORY_H_
#define ZLOG_STRIPE_HISTORY_H_
#include <map>
#include <rados/librados.hpp>

class StripeHistory {
 public:
  void AddStripe(uint64_t position, int width);
  ceph::bufferlist Serialize() const;
  int Deserialize(ceph::bufferlist& bl);
  bool Empty() const;
  int FindStripeSize(uint64_t position) const;
  int LatestStripe() const;

 private:
  std::map<uint64_t, uint32_t> history_;
};

#endif
