#include "log_impl.h"

#include <iostream>

#include "proto/zlog.pb.h"

namespace zlog {

Stream::~Stream() {}

int LogImpl::MultiAppend(const Slice& data,
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

    std::string out_data;
    {
      assert(hdr.IsInitialized());
      uint32_t buf_size = hdr.ByteSize();
      char buf[buf_size];
      assert(hdr.SerializeToArray(buf, buf_size));
      uint32_t be_buf_size = htonl(buf_size);
      out_data.append((char*)&be_buf_size, sizeof(be_buf_size));
      out_data.append(buf, sizeof(buf));
      out_data.append(data.data(), data.size());
    }

    uint64_t epoch;
    std::string oid;
    mapper_.FindObject(position, &oid, &epoch);

    ret = be->Write(oid, Slice(out_data), epoch, position);
    if (ret < 0 && ret != -EFBIG) {
      std::cerr << "append: failed ret " << ret << std::endl;
      return ret;
    }

    if (ret == Backend::ZLOG_OK) {
      if (pposition)
        *pposition = position;
      return 0;
    }

    if (ret == Backend::ZLOG_STALE_EPOCH) {
      ret = RefreshProjection();
      if (ret)
        return ret;
      continue;
    }

    assert(ret == Backend::ZLOG_READ_ONLY);
  }
  assert(0);
}

int LogImpl::StreamHeader(const std::string& entry, std::set<uint64_t>& stream_ids,
    size_t *header_size)
{
  if (entry.size() <= sizeof(uint32_t))
    return -EINVAL;

  const char *data = entry.data();

  uint32_t hdr_len = ntohl(*((uint32_t*)data));
  if (hdr_len > 512) // TODO something reasonable...?
    return -EINVAL;

  if ((sizeof(uint32_t) + hdr_len) > entry.size())
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

int LogImpl::StreamMembership(std::set<uint64_t>& stream_ids, uint64_t position)
{
  std::string entry;
  int ret = Read(position, &entry);
  if (ret)
    return ret;

  ret = StreamHeader(entry, stream_ids);

  return ret;
}

int LogImpl::StreamMembership(uint64_t epoch, std::set<uint64_t>& stream_ids, uint64_t position)
{
  std::string entry;
  int ret = Read(epoch, position, &entry);
  if (ret)
    return ret;

  ret = StreamHeader(entry, stream_ids);

  return ret;
}

class StreamImpl : public zlog::Stream {
 public:
  uint64_t stream_id;
  zlog::LogImpl *log;

  std::set<uint64_t> pos;
  std::set<uint64_t>::const_iterator prevpos;
  std::set<uint64_t>::const_iterator curpos;

  int Append(const Slice& data, uint64_t *pposition = NULL) override;
  int ReadNext(std::string *data, uint64_t *pposition = NULL) override;
  int Reset() override;
  int Sync() override;
  uint64_t Id() const override;
  std::vector<uint64_t> History() const override;
};

std::vector<uint64_t> StreamImpl::History() const
{
  std::vector<uint64_t> ret;
  for (auto it = pos.cbegin(); it != pos.cend(); it++)
    ret.push_back(*it);
  return ret;
}

int StreamImpl::Append(const Slice& data, uint64_t *pposition)
{
  std::set<uint64_t> stream_ids;
  stream_ids.insert(stream_id);
  return log->MultiAppend(data, stream_ids, pposition);
}

int StreamImpl::ReadNext(std::string *data, uint64_t *pposition)
{
  if (curpos == pos.cend())
    return -EBADF;

  assert(!pos.empty());

  uint64_t pos = *curpos;

  std::string entry;
  int ret = log->Read(pos, &entry);
  if (ret)
    return ret;

  size_t header_size;
  std::set<uint64_t> stream_ids;
  ret = log->StreamHeader(entry, stream_ids, &header_size);
  if (ret)
    return -EIO;

  assert(stream_ids.find(stream_id) != stream_ids.end());

  data->assign(entry.data() + header_size, entry.size() - header_size);

  if (pposition)
    *pposition = pos;

  prevpos = curpos;
  curpos++;

  return 0;
}

int StreamImpl::Reset()
{
  curpos = pos.cbegin();
  return 0;
}

/*
 * Optimizations:
 *   - follow backpointers
 */
int StreamImpl::Sync()
{
  /*
   * First contact the sequencer to find out what log position corresponds to
   * the tail of the stream, and then synchronize up to that position.
   */
  std::set<uint64_t> stream_ids;
  stream_ids.insert(stream_id);

  std::map<uint64_t, std::vector<uint64_t>> stream_backpointers;

  int ret = log->CheckTail(stream_ids, stream_backpointers, NULL, false);
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
    assert(pos.empty());
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
  if (!pos.empty()) {
    auto it = pos.crbegin();
    assert(it != pos.crend());
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
      ret = log->StreamMembership(stream_ids, stream_tail);
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
        ret = log->Fill(stream_tail);
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

  pos.insert(updates.begin(), updates.end());

  if (curpos == pos.cend()) {
    if (prevpos == pos.cend()) {
      curpos = pos.cbegin();
      assert(curpos != pos.cend());
    } else {
      curpos = prevpos;
      curpos++;
      assert(curpos != pos.cend());
    }
  }

  return 0;
}

uint64_t StreamImpl::Id() const
{
  return stream_id;
}

/*
 * FIXME:
 *  - Looks like a memory leak on the StreamImpl
 */
int LogImpl::OpenStream(uint64_t stream_id, Stream **streamptr)
{
  StreamImpl *impl = new StreamImpl;

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

  *streamptr = impl;

  return 0;
}

}
