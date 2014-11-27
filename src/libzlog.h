#ifndef LIBZLOG_ZLOG_H
#define LIBZLOG_ZLOG_H
#include <rados/librados.hpp>
#include "libseqr.h"

namespace zlog {

class Log {
 public:
  Log() {}

  /*
   * Set a new projection.
   */
  int SetProjection(uint64_t *pepoch);

  /*
   * Get the current projection.
   */
  int GetProjection(uint64_t *pepoch);

  /*
   * Find the maximum position written.
   */
  int FindMaxPosition(uint64_t epoch, uint64_t *pposition);

  /*
   * Seal all storage devices.
   */
  int Seal(uint64_t epoch);

  /*
   * Find and optionally increment the current tail position.
   */
  int CheckTail(uint64_t *pposition, bool increment = false);

  /*
   * Append data to the log and return its position.
   */
  int Append(ceph::bufferlist& data, uint64_t *pposition = NULL);

  /*
   * Mark a position as unused.
   */
  int Fill(uint64_t position);

  /*
   *
   */
   int Read(uint64_t position, ceph::bufferlist& bl);

  /*
   * Create a new log.
   */
  static int Create(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, Log& log);

  /*
   * Open an existing log.
   */
  static int Open(librados::IoCtx& ioctx, const std::string& name,
      SeqrClient *seqr, Log& log);

  /*
   * Open an existing log or create it if it doesn't exist.
   */
  static int OpenOrCreate(librados::IoCtx& ioctx, const std::string& name,
      int stripe_size, SeqrClient *seqr, Log& log) {
    int ret = Open(ioctx, name, seqr, log);
    if (ret != -ENOENT)
      return ret;
    ret = Create(ioctx, name, stripe_size, seqr, log);
    if (ret == 0)
      return Open(ioctx, name, seqr, log);
    return ret;
  }

 private:
  Log(const Log& rhs);
  Log& operator=(const Log& rhs);

  int RefreshProjection();

  static std::string metalog_oid_from_name(const std::string& name);
  std::string slot_to_oid(int i);
  std::string position_to_oid(uint64_t position);

  librados::IoCtx *ioctx_;
  std::string pool_;
  std::string name_;
  std::string metalog_oid_;
  int stripe_size_;
  SeqrClient *seqr;
  uint64_t epoch_;
};

}

#endif
