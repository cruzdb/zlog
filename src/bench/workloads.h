#ifndef ZLOG_SRC_BENCH_WORKLOADS_H
#define ZLOG_SRC_BENCH_WORKLOADS_H
#include "workload.h"
#include <rados/cls_zlog_bench_client.h>

//#define BENCH_DEBUG

// bytestream stripe group size 16mb
#define MAX_OBJECT_SIZE (1ULL<<24)

/*
 * MapN1:
 *  - a log entry maps to one of N distinct objects (round-robin)
 *  - the log entry is stored in obj.omap[seq]
 *
 * Mapping:
 *  - log[seq] => obj.[seq % stripe_width].omap[seq]
 *  - wraps to new stripe group after MAX_OBJECT_SIZE
 */
class MapN1_Workload : public Workload {
 public:
  MapN1_Workload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history,
      std::string& prefix, int tp_sec, StorageInterface interface,
      bool use_stripe_group) :
    Workload(op_history, qdepth, entry_size, prefix, tp_sec, interface),
    ioctx_(ioctx), stripe_width_(stripe_width), use_stripe_group_(use_stripe_group)
  {
    entries_per_stripe_group_ = (MAX_OBJECT_SIZE / entry_size_) * stripe_width_;
    assert(interface_ == VANILLA);
  }

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) {

    // target object (e.g. seq=127 => prefix.log_mapN1.3.omap[127])
    std::stringstream oid;
    size_t stripe_index = seq % stripe_width_;
    if (use_stripe_group_) {
      size_t stripe_group = seq / entries_per_stripe_group_;
      oid << prefix_ << "log_mapN1." << stripe_group << "." << stripe_index;
    } else
      oid << prefix_ << "log_mapN1." << stripe_index;

    // target omap key (key = seq)
    std::stringstream key;
    key << seq;

    // omap set op
    librados::ObjectWriteOperation op;
    std::map<std::string, ceph::bufferlist> kvs;
    kvs[key.str()] = bl;
    op.omap_set(kvs);

#ifdef BENCH_DEBUG
    std::stringstream kvs_dump;

    for (auto& entry : kvs) {
      kvs_dump << "key=" << entry.first << " "
               << "val=bl/" << entry.second.length() << " ";
    }

    std::cout << "workload=mapN1" << " "
              << "seq=" << seq << " "
              << "obj=" << oid.str() << " "
              << "omap_set: " << kvs_dump.str()
              << std::endl;
#endif

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_operate(oid.str(), rc, &op);
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entries_per_stripe_group_;
  bool use_stripe_group_;
};

/*
 * Map11:
 *  - a log entry maps to a distinct object
 *  - the log entry is stored in obj.omap["entry"]
 *
 * Mapping:
 *  - log[seq] => obj.seq.omap["entry"]
 */
class Map11_Workload : public Workload {
 public:
  Map11_Workload(librados::IoCtx *ioctx, size_t entry_size,
      int qdepth, OpHistory *op_history, std::string& prefix,
      int tp_sec, StorageInterface interface) :
    Workload(op_history, qdepth, entry_size, prefix, tp_sec, interface),
    ioctx_(ioctx)
  {
    assert(interface_ == VANILLA);
  }

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) {

    // target object (e.g. seq=127 => prefix.log_map11.127)
    std::stringstream oid;
    oid << prefix_ << "log_map11." << seq;

    // omap set op
    librados::ObjectWriteOperation op;
    std::map<std::string, ceph::bufferlist> kvs;
    kvs["entry"] = bl;
    op.omap_set(kvs);

#ifdef BENCH_DEBUG
    std::stringstream kvs_dump;

    for (auto& entry : kvs) {
      kvs_dump << "key=" << entry.first << " "
               << "val=bl/" << entry.second.length() << " ";
    }

    std::cout << "workload=map11" << " "
              << "seq=" << seq << " "
              << "obj=" << oid.str() << " "
              << "omap_set: " << kvs_dump.str()
              << std::endl;
#endif

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_operate(oid.str(), rc, &op);
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
};

/*
 * ByteStream11:
 *  - a log entry maps to a distinct object
 *  - the log entry is stored in obj.write(...)
 *
 * Mapping:
 *  - log[seq] => obj.seq.write(...)
 */
class ByteStream11_Workload : public Workload {
 public:
  ByteStream11_Workload(librados::IoCtx *ioctx, size_t entry_size,
      int qdepth, OpHistory *op_history, std::string& prefix,
      int tp_sec, StorageInterface interface) :
    Workload(op_history, qdepth, entry_size, prefix, tp_sec, interface),
    ioctx_(ioctx)
  {
    assert(interface_ == VANILLA);
  }

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) {

    // target object (e.g. seq=127 => prefix.log_bytestream11.127)
    std::stringstream oid;
    oid << prefix_ << "log_bytestream11." << seq;

#ifdef BENCH_DEBUG
    std::cout << "workload=bytestream11" << " "
              << "seq=" << seq << " "
              << "obj=" << oid.str() << " "
              << "off=0 (write_full)" << " "
              << "data=bl/" << bl.length()
              << std::endl;
#endif

    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_write_full(oid.str(), rc, bl);
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
};

/*
 * ByteStreamN1Write:
 *  - a log entry maps to one of N distinct objects (round-robin)
 *  - the log entry is stored at a fixed offset in the object
 *
 * Mapping:
 *  - select object: log[seq] => obj.[seq % stripe_width]
 *      - select offset: obj.write(seq / stripe_width * entry_size)
 *  - wrap to new stripe group after MAX_OBJECT_SIZE limit is reached
 */
class ByteStreamN1Write_Workload : public Workload {
 public:
  ByteStreamN1Write_Workload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history,
      std::string& prefix, int tp_sec, StorageInterface interface,
      bool use_stripe_group) :
    Workload(op_history, qdepth, entry_size, prefix, tp_sec, interface),
    ioctx_(ioctx), stripe_width_(stripe_width), use_stripe_group_(use_stripe_group)
  {
    entries_per_stripe_group_ = (MAX_OBJECT_SIZE / entry_size_) * stripe_width_;
    assert(interface_ == VANILLA);
  }

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) {

    // target object (e.g. seq=127 => prefix.log_mapN1.3)
    std::stringstream oid;
    size_t stripe_index = seq % stripe_width_;
    if (use_stripe_group_) {
      size_t stripe_group = seq / entries_per_stripe_group_;
      oid << prefix_ << "log_bytestreamN1write." << stripe_group << "." << stripe_index;
    } else
      oid << prefix_ << "log_bytestreamN1write." << stripe_index;

    // compute offset within object
    uint64_t offset = seq / stripe_width_ * entry_size_;
    if (use_stripe_group_)
      offset %= MAX_OBJECT_SIZE;

#ifdef BENCH_DEBUG
    std::cout << "workload=bytestreamN1write" << " "
              << "seq=" << seq << " "
              << "obj=" << oid.str() << " "
              << "off=" << offset << " "
              << "data=bl/" << bl.length()
              << std::endl;
#endif
    
    //  submit the io
    *submitted_ns = getns();
    int ret = ioctx_->aio_write(oid.str(), rc, bl, bl.length(), offset);
    assert(ret == 0);
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entries_per_stripe_group_;
  bool use_stripe_group_;
};

/*
 * ByteStreamN1Append:
 *  - a log entry maps to one of N distinct objects (round-robin)
 *  - the log entry is append to the object
 *
 * Mapping:
 *  - select object: log[seq] => obj.[seq % stripe_width]
 *  - perform append
 */
class ByteStreamN1Append_Workload : public Workload {
 public:
  ByteStreamN1Append_Workload(librados::IoCtx *ioctx, size_t stripe_width,
      size_t entry_size, int qdepth, OpHistory *op_history,
      std::string& prefix, int tp_sec, StorageInterface interface,
      bool use_stripe_group) :
    Workload(op_history, qdepth, entry_size, prefix, tp_sec, interface),
    ioctx_(ioctx), stripe_width_(stripe_width), use_stripe_group_(use_stripe_group)
  {
    entries_per_stripe_group_ = (MAX_OBJECT_SIZE / entry_size_) * stripe_width_;
    assert(interface_ == VANILLA ||
        interface_ == CLS_NO_INDEX ||
        interface_ == CLS_CHECK_EPOCH);

    // init objects
    if (interface_ == CLS_CHECK_EPOCH) {
      assert(!use_stripe_group_);
      std::cout << "initializing objects..." << std::endl;
      for (int i = 0; i < stripe_width_; i++) {
        std::stringstream oid;
        oid << prefix_ << "log_bytestreamN1append." << i;
        librados::ObjectWriteOperation op;
        zlog_bench::cls_zlog_bench_append_init(op);
        int ret = ioctx_->operate(oid.str(), &op);
        assert(ret == 0);
      }
    }
  }

  void gen_op(librados::AioCompletion *rc, uint64_t *submitted_ns,
      ceph::bufferlist& bl) {

    // target object (e.g. seq=127 => prefix.log_mapN1.3)
    std::stringstream oid;
    size_t stripe_index = seq % stripe_width_;
    if (use_stripe_group_) {
      size_t stripe_group = seq / entries_per_stripe_group_;
      oid << prefix_ << "log_bytestreamN1append." << stripe_group << "." << stripe_index;
    } else
      oid << prefix_ << "log_bytestreamN1append." << stripe_index;

#ifdef BENCH_DEBUG
    std::cout << "workload=bytestreamN1append" << " "
              << "seq=" << seq << " "
              << "obj=" << oid.str() << " "
              << "off=? (append)" <<  " "
              << "data=bl/" << bl.length()
              << std::endl;
#endif
    
    //  submit the io
    *submitted_ns = getns();

    switch (interface_) {
    case CLS_NO_INDEX:
      {
        librados::ObjectWriteOperation op;
        zlog_bench::cls_zlog_bench_append(op, 123, seq, bl);
        int ret = ioctx_->aio_operate(oid.str(), rc, &op);
        assert(ret == 0);
      }
      break;

    case CLS_CHECK_EPOCH:
      {
        librados::ObjectWriteOperation op;
        zlog_bench::cls_zlog_bench_append_check_epoch(op, 123, seq, bl);
        int ret = ioctx_->aio_operate(oid.str(), rc, &op);
        assert(ret == 0);
      }
      break;

    case VANILLA:
      {
        int ret = ioctx_->aio_append(oid.str(), rc, bl, bl.length());
        assert(ret == 0);
      }
      break;

    default:
      assert(0);
      exit(-1);
    }
  }

 private:
  librados::IoCtx *ioctx_;
  size_t stripe_width_;
  size_t entries_per_stripe_group_;
  bool use_stripe_group_;
};

#endif
