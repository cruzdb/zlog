#ifndef ZLOG_LOG_MAPPER_H_
#define ZLOG_LOG_MAPPER_H_
#include "stripe_history.h"
#include <atomic>
#include <mutex>
#include <vector>
#include <string>

class LogMapper {
 public:
  void FindObject(uint64_t position, std::string *oid, uint64_t *epoch);

  void LatestObjectSet(std::vector<std::string>& objects,
      const StripeHistory& history);

  void SetName(const std::string& log_name) {
    log_name_ = log_name;
  }

  uint64_t Epoch();

  void SetHistory(const StripeHistory& history, uint64_t epoch);

  int CurrentStripeWidth();

 private:
  std::string SlotToOid(uint64_t epoch, int slot) const;

  std::string log_name_;
  StripeHistory history_;

  std::mutex lock_;

  std::atomic<uint64_t> epoch_;
};

#endif
