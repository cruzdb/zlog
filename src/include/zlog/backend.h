#pragma once
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include "zlog/slice.h"

namespace zlog {

// All methods return 0 on success, or a negative error code on failure. The
// following error codes are common for all methods, unless otherwise specified
// in a method comment. Each method comment also lists any return codes with
// special meaning.
//
// -EINVAL
//   - Failed to decode an input message
//   - Invalid parameter
// -EIO
//   - Corrupted data or invalid states
// -ESPIPE
//   - Stale epoch
// -ENOENT
//   - object doesn't exist
//
// All methods should be thread-safe.
class Backend {
 public:
  virtual ~Backend() {}

  static int Load(const std::string& scheme,
      const std::map<std::string, std::string>& opts,
      std::shared_ptr<Backend>& backend);

  // Initialize the backend.
  //
  // This method is called when the backend is loaded as a dynamic module. In
  // that case the log implementation has only a `Backend*` and thus any
  // backend-specific initialization must be completed through a generic
  // interface. The backend should be able to initialize itself based on the set
  // of provided options, and each backend should document the set of options
  // that it expects. Initialization with this method is optional, for instance
  // when explicitly creating backend instances of a particular type, the
  // dervied classes may have more convenient interfaces for instantiation.
  virtual int Initialize(
      const std::map<std::string, std::string>& options) = 0;

  virtual std::map<std::string, std::string> meta() = 0;

  // log management
 public:

  // Create a new, empty log with the given name.
  //
  // -EEXIST
  //   - log with name already exists
  virtual int CreateLog(const std::string& name,
      const std::string& initial_view) = 0;

  // Return a context for constructing object names.
  //
  // -ENOENT
  //   - log doesn't exist (or has been deleted)
  virtual int OpenLog(const std::string& name,
      std::string& hoid, std::string& prefix) = 0;

  // view management
 public:

  // Read log views.
  //
  // -ENOENT
  //   - object not initialized (or doens't exist)
  virtual int ReadViews(const std::string& hoid,
      uint64_t epoch, std::map<uint64_t, std::string>& views) = 0;

  // Create a new view.
  //
  // -EINVAL
  //   - initialize with non-zero epoch
  //   - proposed epoch is not stored-epoch + 1
  virtual int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) = 0;

  // log data interfaces
 public:

  // Read a log entry.
  //
  // -ENOENT
  //   - position not written (nor invalidated)
  // -ENODATA
  //   - position has been invalidated (fill or trim)
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data) = 0;

  // Write a log entry.
  //
  // -EROFS
  //   - position is read-only (written or invalid)
  virtual int Write(const std::string& oid, const Slice& data,
      uint64_t epoch, uint64_t position, uint32_t stride,
      uint32_t max_size) = 0;

  // Invalidate a log entry.
  //
  // -EROFS
  //   - position is read-only (written or invalid)
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) = 0;

  // Force invalidate a log entry.
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size) = 0;

  // Set a new log data object epoch.
  virtual int Seal(const std::string& oid, uint64_t epoch) = 0;

  // Return the maximum position written to a log data object.
  //
  // -ENOENT
  //   - object doesn't exist. seal first.
  // -ESPIPE
  //   - epoch equality failed
  virtual int MaxPos(const std::string& oid, uint64_t epoch,
      uint64_t *pos, bool *empty) = 0;

  // asynchronous variants
 public:

  // See Read()
  virtual int AioRead(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      std::string *data, void *arg,
      std::function<void(void*, int)> callback) = 0;

  // See Write()
  virtual int AioWrite(const std::string& oid, uint64_t epoch,
      uint64_t position, uint32_t stride, uint32_t max_size,
      const Slice& data, void *arg,
      std::function<void(void*, int)> callback) = 0;
};

}
