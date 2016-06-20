#ifndef ZLOG_LOG_MAPPER_H_
#define ZLOG_LOG_MAPPER_H_
#include "stripe_history.h"
#include <vector>
#include <string>

class LogMapper {
 public:
  std::string FindObject(uint64_t position) const;

  void LatestObjectSet(std::vector<std::string>& objects,
      const StripeHistory& history) const;

  void SetName(const std::string& log_name) {
    log_name_ = log_name;
  }

  void SetHistory(const StripeHistory& history) {
    history_ = history;
  }

  int CurrentStripeWidth() const;

 private:
  std::string SlotToOid(uint64_t epoch, int slot) const;

  std::string log_name_;
  StripeHistory history_;
};

#endif
