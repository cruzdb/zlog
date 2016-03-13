#ifndef ZLOG_SRC_BENCH_WORKLOADS_H
#define ZLOG_SRC_BENCH_WORKLOADS_H

class ByteStreamN1Write_Workload : public Workload {
 public:
  ByteStreamN1Write_Workload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history) :
    Workload(op_history, qdepth),
    ioctx_(ioctx),
    stripe_width_(stripe_width),
    entry_size_(entry_size)
  {}

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns) {
    // target object
    std::stringstream oid;
    size_t stripe_offset = seq % stripe_width_;
    oid << "log." << stripe_offset;

    // object offset
    uint64_t offset = seq / stripe_width_ * entry_size_;
    
    // data
    char data[entry_size_];
    ceph::bufferlist bl;
    bl.append(data, entry_size_);

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_write(oid.str(), rc, bl, bl.length(), offset);
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entry_size_;
};

class ByteStreamN1Append_Workload : public Workload {
 public:
  ByteStreamN1Append_Workload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history) :
    Workload(op_history, qdepth),
    ioctx_(ioctx),
    stripe_width_(stripe_width),
    entry_size_(entry_size)
  {}

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns) {
    // target object
    std::stringstream oid;
    size_t stripe_offset = seq % stripe_width_;
    oid << "log." << stripe_offset;
    
    // data
    char data[entry_size_];
    ceph::bufferlist bl;
    bl.append(data, entry_size_);

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_append(oid.str(), rc, bl, bl.length());
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entry_size_;
};

#endif
