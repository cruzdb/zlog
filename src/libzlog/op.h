#pragma once

namespace zlog {

// An operation that targets a specific log position.
class PositionOp {
 public:
  PositionOp(LogImpl *log) :
    log_(log),
    done_(false)
  {}

  PositionOp(LogImpl *log, uint64_t position) :
    log_(log),
    position_(position),
    done_(false)
  {}

 public:
  // Called to set the latest view before invoking the operation. This may be
  // called multiple times if the operation is restarted.
  void set_view(std::shared_ptr<const VersionedView>& view) {
    view_ = view;
  }

  // Returns true if the operation has completed.
  bool done() const {
    return done_;
  }

  // Called by operations to invoke the associated callback and mark the
  // operation as completed. Prefer complete(0) to indicate success.
  void complete(int ret) {
    callback(ret);
    done_ = true;
  }

  // Invoke an operation's callback with the provided return code. Operations
  // typically add additional context. For instance the read operation will
  // provide retrieved data.
  virtual void callback(int ret) = 0;

 public:
  // Ensure that the operation has a position. If the operation is not
  // configured with a position then fetch_position is invoked. False is
  // returned if the operation should not continue.
  virtual bool prepare() {
    assert(view_);
    if (need_position()) {
      if (!view_->seq) {
        complete(-EIO);
        return false;
      }
      fetch_position();
    }
    assert(position_);
    return true;
  }

  // Return true if fetch_position should be invoked. Operations like append
  // override this because they can cache the position between restarts.
  virtual bool need_position() const {
    return !position_;
  }

  virtual void fetch_position() {}

  // The main operation
  virtual void run() = 0;

 protected:
  LogImpl *log_;
  boost::optional<uint64_t> position_;
  bool done_;
  std::shared_ptr<const VersionedView> view_;
};

// An operation that performs i/o on a target position.
class MappedPositionOp : public PositionOp {
 public:
  MappedPositionOp(LogImpl *log) :
    PositionOp(log)
  {}

  MappedPositionOp(LogImpl *log, uint64_t position) :
    PositionOp(log, position)
  {}

 public:
  bool prepare() override {
    // first ensure that we have a position
    if (!PositionOp::prepare()) {
      return false;
    } else {
      // map the position
      assert(position_);
      oid_ = log_->view_mgr->map(view_, *position_);
      if (oid_) {
        // with a mapping, proceed
        return true;
      } else {
        // extend the log and restart the operation
        int ret = log_->view_mgr->try_expand_view(*position_);
        if (ret) {
          complete(ret);
        }
        return false;
      }
    }
  }

  // Common error handling performed by run()
  void handle_common_ret(int ret) {
    if (ret == 0) {
      complete(0);

    } else if (ret == -ESPIPE) {
      // update the view which appears to be out-of-date.
      // TODO: we also need to make sure that we timeout eventually and drive
      // the view forward in case some objects are stuck with a newer epoch but
      // a view with the epoch is lacking.
      log_->view_mgr->update_current_view(view_->epoch());

    } else if (ret == -ENOENT) {
      // it is possible that the operation is racing with initialization of
      // objects in a new stripe and this operation observes a missing object.
      // in this case we can drive initialization ourselves and restart.
      int ret = log_->backend->Seal(*oid_, view_->epoch());
      if (ret && ret != -ESPIPE) {
        complete(ret);
      }

    } else {
      complete(ret);
    }
  }

 protected:
  boost::optional<std::string> oid_;
};

// Queries the sequencer for the current tail position.
class TailOp final : public PositionOp {
 public:
  TailOp(LogImpl *log, std::function<void(int, uint64_t)> cb) :
    PositionOp(log),
    cb_(cb)
  {}

 public:
  bool need_position() const override {
    return true;
  }

  void fetch_position() override {
    position_ = view_->seq->check_tail(false);
  }

  void run() override {
    complete(0);
  }

  void callback(int ret) override {
    if (ret == 0) {
      assert(position_);
    }
    if (cb_) {
      cb_(ret, position_ ? *position_ : 0);
    }
  }

 private:
  const std::function<void(int, uint64_t)> cb_;
};

//
class TrimToOp final : public PositionOp {
 public:
  TrimToOp(LogImpl *log, uint64_t position,
      std::function<void(int)> cb) :
    PositionOp(log, position),
    cb_(cb)
  {}

 public:
  void run() override {
    // we are invalidating the range [0, position_] (inclusive). this results in
    // a _valid range_ of [_position+1, ...) which is why we advance the valid
    // position to position_ + 1.
    if (*position_ >= view_->object_map().min_valid_position()) {
      int ret = log_->view_mgr->advance_min_valid_position(*position_ + 1);
      complete(ret);
    } else {
      complete(0);
    }
  }

  void callback(int ret) override {
    if (cb_) {
      cb_(ret);
    }
  }

 private:
  std::function<void(int)> cb_;
};

// Read data from a target log position.
class ReadOp final : public MappedPositionOp {
 public:
  ReadOp(LogImpl *log, uint64_t position,
      std::function<void(int, std::string&)> cb) :
    MappedPositionOp(log, position),
    cb_(cb)
  {}

 public:
  void run() override {
    int ret = log_->backend->Read(*oid_, view_->epoch(), *position_, &data_);
    if (ret == -ERANGE) {
      // the log position hasn't been written
      complete(-ENOENT);
    } else {
      handle_common_ret(ret);
    }
  }

  void callback(int ret) override {
    if (cb_) {
      cb_(ret, data_);
    }
  }

 private:
  // TODO: how to move data into callback
  std::string data_;
  std::function<void(int, std::string&)> cb_;
};

// Fill a target log position.
class FillOp final : public MappedPositionOp {
 public:
  FillOp(LogImpl *log, uint64_t position, std::function<void(int)> cb) :
    MappedPositionOp(log, position),
    cb_(cb)
  {}

 public:
  void run() override {
    int ret = log_->backend->Fill(*oid_, view_->epoch(), *position_);
    handle_common_ret(ret);
  }

  void callback(int ret) override {
    if (cb_) {
      cb_(ret);
    }
  }

 private:
  std::function<void(int)> cb_;
};

// Trim a target log position.
class TrimOp final : public MappedPositionOp {
 public:
  TrimOp(LogImpl *log, uint64_t position, std::function<void(int)> cb) :
    MappedPositionOp(log, position),
    cb_(cb)
  {}

 public:
  void run() override {
    int ret = log_->backend->Trim(*oid_, view_->epoch(), *position_, false, false);
    handle_common_ret(ret);
  }

  void callback(int ret) override {
    if (cb_) {
      cb_(ret);
    }
  }

 private:
  std::function<void(int)> cb_;
};

// Append data to the end of the log.
class AppendOp final : public MappedPositionOp {
 public:
  AppendOp(LogImpl *log, const std::string& data,
      std::function<void(int, uint64_t)> cb) :
    MappedPositionOp(log),
    data_(data),
    cb_(cb)
  {}

 public:
  // avoid obtaining a new append position when the view has been updated
  // (e.g. because the mapping was extended), but the sequencer did not
  // change. this is generally a minor optimization. but for completeness,
  // it also handles the edge case in which stripes are configured to hold
  // exactly one log entry. in this case a loop will be created by which the
  // new position doesn't map, the map is extended, and then a new unmapped
  // position is obtained. XXX: of course if the sequencer also changes each
  // time there also may be a loop, but that would be a bigger issue.
  bool need_position() const override {
    return !position_epoch_ || (*position_epoch_ != view_->seq->epoch());
  }

  void fetch_position() override {
    position_ = view_->seq->check_tail(true);
    position_epoch_ = view_->seq->epoch();
  }

  void run() override {
    int ret = log_->backend->Write(*oid_, data_, view_->epoch(), *position_);
    if (ret == -EROFS) {
      // the position was taken. restart with a new position.
      position_epoch_.reset();
    } else {
      handle_common_ret(ret);
    }
  }

  void callback(int ret) override {
    if (cb_) {
      cb_(ret, position_ ? *position_ : uint64_t(0));
    }
  }

 private:
  // TODO: move OR reference / async OR sync?
  std::string data_;
  boost::optional<uint64_t> position_epoch_;
  std::function<void(int, uint64_t)> cb_;
};

}
