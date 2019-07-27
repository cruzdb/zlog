#pragma once
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace zlog {

class Backend {
 public:
  virtual ~Backend() {}

  // TBD. Load, Initialize, and meta will be examined when working on
  // backend-specific options support.
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

 public:
  /**
   * Create a new log.
   *
   * The name of the head object, and a prefix that should be used when
   * constructing data objects, are returned through @hoid_out and @prefix_out,
   * respectively. The prefix created by a backend must be unique and stable
   * such that when a log is opened in the future the same prefix is available.
   *
   * @param name       name of the log
   * @param view       initial log view
   * @param hoid_out   name of the head object
   * @param prefix_out log entry object prefix
   *
   * @return 0 or non-zero
   * -EEXIST log name already exists
   * -EINVAL invalid input
   */
  virtual int CreateLog(const std::string& name, const std::string& view,
      std::string *hoid_out, std::string *prefix_out) = 0;

  /**
   * Open a log.
   *
   * The name of the head object, and a prefix that should be used when
   * constructing data objects, are returned through @hoid_out and @prefix_out,
   * respectively. When a log is created, the view for epoch 1 is written, so
   * clients should start with epoch 2 when using this interface. The prefix
   * returned must be the same prefix returned when the log was created.
   *
   * @param name       name of the log
   * @param hoid_out   name of the head object
   * @param prefix_out log entry object prefix
   *
   * @return 0 or non-zero
   * -ENOENT log name doesn't exist
   * -EINVAL invalid input
   */
  virtual int OpenLog(const std::string& name, std::string *hoid_out,
      std::string *prefix_out) = 0;

  /**
   * List links.
   *
   * @return 0 or non-zero
   * -1 not implemented
   */
  virtual int ListLinks(std::vector<std::string> &loids_out) {
    return -1;
  }

  /**
   * List heads.
   *
   * @return 0 or non-zero
   * -1 not implemented
   */
  virtual int ListHeads(std::vector<std::string> &hoids_out) {
    return -1;
  }

 public:
  /**
   * Read views.
   *
   * Returns the sequence of views associated with the head object starting from
   * the given epoch (inclusive). The maximum number of views returned per call
   * is controlled by the backend implementation.
   *
   * If the epoch requested is 0 then the returned views will contain the view
   * with the latest epoch, provided that the head object contains at least one
   * view.
   *
   * @param hoid      name of the head object
   * @param epoch     starting epoch (inclusive)
   * @param max_views max views to return
   * @param views     the { epoch: view } results
   *
   * @return 0 or non-zero
   * -EINVAL invalid input
   * -ENOENT hoid doesn't exist / needs initialized
   */
  virtual int ReadViews(const std::string& hoid,
      uint64_t epoch, uint32_t max_views,
      std::map<uint64_t, std::string> *views_out) = 0;

  /**
   * Propose a new view.
   *
   * Views are tagged with a numeric epoch starting at one. New views are
   * rejected if the proposed epoch is not the next epoch in sequence (that is,
   * if the proposed epoch != current+1). This permits clients to implement a
   * simple compare-and-exchange transaction to change views.
   *
   * @param hoid  name of the head object
   * @param epoch proposed next epoch
   * @param view  proposed view
   *
   * @return 0 or non-zero
   * -EINVAL invalid input params
   * -ENOENT head object doesn't exist / is not intialized
   * -ESPIPE invalid epoch (try again)
   */
  virtual int ProposeView(const std::string& hoid,
      uint64_t epoch, const std::string& view) = 0;

  /**
   * Generate a unique id.
   *
   * The generated id must be unique to the @hoid log, but implementations may
   * ignore @hoid and generated a globally unique id.
   *
   * @param hoid
   * @param id_out
   *
   * @return 0 or non-zero
   * -EINVAL bad input params
   */
  virtual int uniqueId(const std::string& hoid, uint64_t *id_out) = 0;

 public:
  /**
   * Read a log position.
   *
   * @param oid
   * @param epoch
   * @param position
   * @param data
   *
   * @return 0 or non-zero
   * -EINVAL bad input params, bad input message, bad epoch
   * -ENOENT object doesn't exist / needs init
   * -ESPIPE stale epoch
   * -ERANGE position hasn't been written
   * -ENODATA entry position has been invalidated
   */
  virtual int Read(const std::string& oid, uint64_t epoch,
      uint64_t position, std::string *data_out) = 0;

  /**
   * Write a log position.
   *
   * @param oid
   * @param data
   * @param epoch
   * @param position
   *
   * @return 0 or non-zero
   * -EINVAL bad input params
   * -ENOENT object doesn't exist / needs init
   * -ESPIPE stale epoch
   * -EROFS position exists
   */
  virtual int Write(const std::string& oid, const std::string& data,
      uint64_t epoch, uint64_t position) = 0;

  /**
   * Fill a log position.
   *
   * @param oid
   * @param epoch
   * @param position
   *
   * @return 0 (idempotent) or non-zero
   * -EINVAL bad input params
   * -ENOENT object doesn't exist / needs init
   * -ESPIPE stale epoch
   * -EROFS position exists (and is not invalid)
   */
  virtual int Fill(const std::string& oid, uint64_t epoch,
      uint64_t position) = 0;

  /**
   * Mark positions as unused and reclaim storage space.
   *
   * @param oid
   * @param epoch
   * @param position
   * @param trim_limit
   * @param trim_full
   *
   * @return 0 (idempotent) or non-zero
   * -EINVAL bad input params
   * -ENOENT object doesn't exist / needs init
   * -ESPIPE stale epoch
   */
  virtual int Trim(const std::string& oid, uint64_t epoch,
      uint64_t position, bool trim_limit = false,
      bool trim_full = false) = 0;

  /**
   * Seal / initialize a log entries object.
   *
   * @oid
   * @epoch
   *
   * @return 0 or non-zero
   * -EVINAL invalid input params
   * -ESPIPE epoch <= stored epoch
   */
  virtual int Seal(const std::string& oid, uint64_t epoch) = 0;

  /**
   * Return the maximum position (if any) written to an object.
   *
   * Note that the maximum position includes positions trimmed and filled. In
   * addition, the maximum includes any trim limit that has been set, which may
   * be larger than the addressable position of the object. If a trim limit has
   * been set and no positions have been explicitly written, trimmed, or filled,
   * the object is still reported as non-empty.
   *
   * @param oid
   * @param pos_out
   * @param empty_out
   *
   * @return 0 or non-zero
   * -EINVAL bad input params
   * -ENOENT object doesn't exist / needs init
   */
  virtual int MaxPos(const std::string& oid, uint64_t *pos_out, bool *empty_out) = 0;

  /**
   * Return the size of an object in bytes.
   *
   * Note that a backend may only return an estimate of the size, as an exact
   * measurement may be difficult to calculate.
   *
   * @param oid
   * @param size
   *
   * @return 0 or non-zero
   * -ENOENT object doesn't exist / needs init
   */
  virtual int Stat(const std::string& oid, size_t *size) = 0;
};

}
