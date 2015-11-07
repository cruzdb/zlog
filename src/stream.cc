#include <iostream>
#include <rados/librados.hpp>
#include <rados/cls_zlog_client.h>
#include "libzlog.hpp"
#include "zlog.pb.h"
#include "protobuf_bufferlist_adapter.h"
#include "internal.hpp"

namespace zlog {

int Log::MultiAppend(ceph::bufferlist& data,
    const std::set<uint64_t>& stream_ids, uint64_t *pposition)
{
  for (;;) {
    /*
     * Get a new spot at the tail of the log and return a set of backpointers
     * for the specified streams. The stream ids and backpointers are stored
     * in the header of the entry being appeneded to the log.
     */
    uint64_t position;
    std::map<uint64_t, std::vector<uint64_t>> stream_backpointers;
    int ret = CheckTail(stream_ids, stream_backpointers, &position, true);
    if (ret)
      return ret;

    assert(stream_ids.size() == stream_backpointers.size());

    zlog_proto::EntryHeader hdr;
    size_t index = 0;
    for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
         it != stream_ids.end(); it++) {
      uint64_t stream_id = *it;
      const std::vector<uint64_t>& backpointers = stream_backpointers[index];
      zlog_proto::StreamBackPointer *ptrs = hdr.add_stream_backpointers();
      ptrs->set_id(stream_id);
      for (std::vector<uint64_t>::const_iterator it2 = backpointers.begin();
           it2 != backpointers.end(); it2++) {
        uint64_t pos = *it2;
        ptrs->add_backpointer(pos);
      }
      index++;
    }

    ceph::bufferlist bl;
    pack_msg_hdr<zlog_proto::EntryHeader>(bl, hdr);
    bl.append(data.c_str(), data.length());

    librados::ObjectWriteOperation op;
    zlog::cls_zlog_write(op, epoch_, position, bl);

    std::string oid = position_to_oid(position);
    ret = ioctx_->operate(oid, &op);
    if (ret < 0) {
      std::cerr << "append: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == zlog::CLS_ZLOG_OK) {
      if (pposition)
        *pposition = position;
      return 0;
    }

    if (ret == zlog::CLS_ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == zlog::CLS_ZLOG_READ_ONLY);
  }
  assert(0);
}

int Log::StreamHeader(ceph::bufferlist& bl, std::set<uint64_t>& stream_ids,
    size_t *header_size)
{
  if (bl.length() <= sizeof(uint32_t))
    return -EINVAL;

  const char *data = bl.c_str();

  uint32_t hdr_len = ntohl(*((uint32_t*)data));
  if (hdr_len > 512) // TODO something reasonable...?
    return -EINVAL;

  if ((sizeof(uint32_t) + hdr_len) > bl.length())
    return -EINVAL;

  zlog_proto::EntryHeader hdr;
  if (!hdr.ParseFromArray(data + sizeof(uint32_t), hdr_len))
    return -EINVAL;

  if (!hdr.IsInitialized())
    return -EINVAL;

  std::set<uint64_t> ids;
  for (int i = 0; i < hdr.stream_backpointers_size(); i++) {
    const zlog_proto::StreamBackPointer& ptr = hdr.stream_backpointers(i);
    ids.insert(ptr.id());
  }

  if (header_size)
    *header_size = sizeof(uint32_t) + hdr_len;

  stream_ids.swap(ids);

  return 0;
}

int Log::StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position)
{
  ceph::bufferlist bl;
  int ret = Read(position, bl);
  if (ret)
    return ret;

  ret = StreamHeader(bl, stream_ids);

  return ret;
}

int Log::StreamMembership(uint64_t epoch, std::set<uint64_t>& stream_ids, uint64_t position)
{
  ceph::bufferlist bl;
  int ret = Read(epoch, position, bl);
  if (ret)
    return ret;

  ret = StreamHeader(bl, stream_ids);

  return ret;
}

struct Log::Stream::StreamImpl {
  uint64_t stream_id;
  Log *log;

  std::set<uint64_t> pos;
  std::set<uint64_t>::const_iterator prevpos;
  std::set<uint64_t>::const_iterator curpos;
};

std::vector<uint64_t> Log::Stream::History() const
{
  Log::Stream::StreamImpl *impl = this->impl;

  std::vector<uint64_t> ret;
  for (auto it = impl->pos.cbegin(); it != impl->pos.cend(); it++)
    ret.push_back(*it);
  return ret;
}

int Log::Stream::Append(ceph::bufferlist& data, uint64_t *pposition)
{
  Log::Stream::StreamImpl *impl = this->impl;
  std::set<uint64_t> stream_ids;
  stream_ids.insert(impl->stream_id);
  return impl->log->MultiAppend(data, stream_ids, pposition);
}

int Log::Stream::ReadNext(ceph::bufferlist& bl, uint64_t *pposition)
{
  Log::Stream::StreamImpl *impl = this->impl;

  if (impl->curpos == impl->pos.cend())
    return -EBADF;

  assert(!impl->pos.empty());

  uint64_t pos = *impl->curpos;

  ceph::bufferlist bl_out;
  int ret = impl->log->Read(pos, bl_out);
  if (ret)
    return ret;

  size_t header_size;
  std::set<uint64_t> stream_ids;
  ret = impl->log->StreamHeader(bl_out, stream_ids, &header_size);
  if (ret)
    return -EIO;

  assert(stream_ids.find(impl->stream_id) != stream_ids.end());

  // FIXME: how to create this view more efficiently?
  const char *data = bl_out.c_str();
  bl.append(data + header_size, bl_out.length() - header_size);

  if (pposition)
    *pposition = pos;

  impl->prevpos = impl->curpos;
  impl->curpos++;

  return 0;
}

int Log::Stream::Reset()
{
  Log::Stream::StreamImpl *impl = this->impl;
  impl->curpos = impl->pos.cbegin();
  return 0;
}

/*
 * Optimizations:
 *   - follow backpointers
 */
int Log::Stream::Sync()
{
  Log::Stream::StreamImpl *impl = this->impl;
  const uint64_t stream_id = impl->stream_id;

  /*
   * First contact the sequencer to find out what log position corresponds to
   * the tail of the stream, and then synchronize up to that position.
   */
  std::set<uint64_t> stream_ids;
  stream_ids.insert(stream_id);

  std::map<uint64_t, std::vector<uint64_t>> stream_backpointers;

  int ret = impl->log->CheckTail(stream_ids, stream_backpointers, NULL, false);
  if (ret)
    return ret;

  assert(stream_backpointers.size() == 1);
  const std::vector<uint64_t>& backpointers = stream_backpointers.at(stream_id);

  /*
   * The tail of the stream is the maximum log position handed out by the
   * sequencer for this particular stream. When the tail of a stream is
   * incremented the position is placed onto the list of backpointers. Thus
   * the max position in the backpointers set for a stream is the tail
   * position of the stream.
   *
   * If the current set of backpointers is empty, then the stream is empty and
   * there is nothing to do.
   */
  std::vector<uint64_t>::const_iterator bpit =
    std::max_element(backpointers.begin(), backpointers.end());
  if (bpit == backpointers.end()) {
    assert(impl->pos.empty());
    return 0;
  }
  uint64_t stream_tail = *bpit;

  /*
   * Avoid sync in log ranges that we've already processed by examining the
   * maximum stream position that we know about. If our local stream history
   * is empty then use the beginning of the log as the low point.
   *
   * we are going to search for stream entries between stream_tail (the last
   * position handed out by the sequencer for this stream), and the largest
   * stream position that we (the client) knows about. if we do not yet know
   * about any stream positions then we'll search down until position zero.
   */
  bool has_known = false;
  uint64_t known_stream_tail;
  if (!impl->pos.empty()) {
    auto it = impl->pos.crbegin();
    assert(it != impl->pos.crend());
    known_stream_tail = *it;
    has_known = true;
  }

  assert(!has_known || known_stream_tail <= stream_tail);
  if (has_known && known_stream_tail == stream_tail)
    return 0;

  std::set<uint64_t> updates;
  for (;;) {
    if (has_known && stream_tail == known_stream_tail)
      break;
    for (;;) {
      std::set<uint64_t> stream_ids;
      ret = impl->log->StreamMembership(stream_ids, stream_tail);
      if (ret == 0) {
        // save position if it belongs to this stream
        if (stream_ids.find(stream_id) != stream_ids.end())
          updates.insert(stream_tail);
        break;
      } else if (ret == -EINVAL) {
        // skip non-stream entries
        break;
      } else if (ret == -EFAULT) {
        // skip invalidated entries
        break;
      } else if (ret == -ENODEV) {
        // fill entries unwritten entries
        ret = impl->log->Fill(stream_tail);
        if (ret == 0) {
          // skip invalidated entries
          break;
        } else if (ret == -EROFS) {
          // retry
          continue;
        } else
          return ret;
      } else
        return ret;
    }
    if (!has_known && stream_tail == 0)
      break;
    stream_tail--;
  }

  if (updates.empty())
    return 0;

  impl->pos.insert(updates.begin(), updates.end());

  if (impl->curpos == impl->pos.cend()) {
    if (impl->prevpos == impl->pos.cend()) {
      impl->curpos = impl->pos.cbegin();
      assert(impl->curpos != impl->pos.cend());
    } else {
      impl->curpos = impl->prevpos;
      impl->curpos++;
      assert(impl->curpos != impl->pos.cend());
    }
  }

  return 0;
}

uint64_t Log::Stream::Id() const
{
  Log::Stream::StreamImpl *impl = this->impl;
  return impl->stream_id;
}

int Log::OpenStream(uint64_t stream_id, Stream& stream)
{
  assert(!stream.impl);

  Log::Stream::StreamImpl *impl = new Log::Stream::StreamImpl;
  impl->stream_id = stream_id;
  impl->log = this;

  /*
   * Previous position always points to the last position in the stream that
   * was successfully read, except on initialization when it points to the end
   * of the stream.
   */
  impl->prevpos = impl->pos.cend();

  /*
   * Current position always points to the element that is the next to be
   * read, or to the end of the stream if there are no [more] elements in the
   * stream to be read.
   */
  impl->curpos = impl->pos.cbegin();

  stream.impl = impl;

  return 0;
}

extern "C" int zlog_stream_open(zlog_log_t log, uint64_t stream_id,
    zlog_stream_t *pstream)
{
  zlog_log_ctx *log_ctx = (zlog_log_ctx*)log;

  zlog_stream_ctx *stream_ctx = new zlog_stream_ctx;
  stream_ctx->log_ctx = log_ctx;

  int ret = log_ctx->log.OpenStream(stream_id, stream_ctx->stream);
  if (ret) {
    delete stream_ctx;
    return ret;
  }

  *pstream = stream_ctx;

  return 0;
}

extern "C" int zlog_stream_append(zlog_stream_t stream, const void *data,
    size_t len, uint64_t *pposition)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  ceph::bufferlist bl;
  bl.append((char*)data, len);
  return ctx->stream.Append(bl, pposition);
}

extern "C" int zlog_stream_readnext(zlog_stream_t stream, void *data,
    size_t len, uint64_t *pposition)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;

  ceph::bufferlist bl;
  // FIXME: below the buffer is added to avoid double copies. However, in
  // ReadNext we have to create a view of the data read to remove the header.
  // It isn't clear how to do that without the copies. As a fix for now we
  // just force the case where the bufferlist has to be resized.
#if 0
  ceph::bufferptr bp = ceph::buffer::create_static(len, (char*)data);
  bl.push_back(bp);
#endif

  int ret = ctx->stream.ReadNext(bl, pposition);

  if (ret >= 0) {
    if (bl.length() > len)
      return -ERANGE;
    if (bl.c_str() != data)
      bl.copy(0, bl.length(), (char*)data);
    ret = bl.length();
  }

  return ret;
}

extern "C" int zlog_stream_reset(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream.Reset();
}

extern "C" int zlog_stream_sync(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream.Sync();
}

extern "C" uint64_t zlog_stream_id(zlog_stream_t stream)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;
  return ctx->stream.Id();
}

extern "C" size_t zlog_stream_history(zlog_stream_t stream, uint64_t *pos, size_t len)
{
  zlog_stream_ctx *ctx = (zlog_stream_ctx*)stream;

  std::vector<uint64_t> history = ctx->stream.History();
  size_t size = history.size();
  if (pos && size <= len)
    std::copy(history.begin(), history.end(), pos);

  return size;
}

extern "C" int zlog_stream_membership(zlog_log_t log,
    uint64_t *stream_ids, size_t len, uint64_t position)
{
  zlog_log_ctx *ctx = (zlog_log_ctx*)log;

  std::set<uint64_t> ids;
  int ret = ctx->log.StreamMembership(ids, position);
  if (ret)
    return ret;

  size_t size = ids.size();
  if (size <= len) {
    std::vector<uint64_t> tmp;
    for (auto it = ids.begin(); it != ids.end(); it++)
      tmp.push_back(*it);
    std::copy(tmp.begin(), tmp.end(), stream_ids);
  }

  return size;
}

}
