#include <set>
#include <iostream>
#include <map>
#include <mutex>
#include <boost/asio.hpp>
#include "libseqr.h"
#include "proto/zlog.pb.h"

namespace zlog {

void SeqrClient::Connect() {
  for (channel *chan : channels_) {
    boost::asio::ip::tcp::resolver resolver(chan->io_service_);
    boost::asio::ip::tcp::resolver::query query(
        boost::asio::ip::tcp::v4(), host_.c_str(), port_);
    boost::asio::ip::tcp::resolver::iterator iterator = resolver.resolve(query);
    chan->socket_.connect(*iterator);
  }
}

int SeqrClient::CheckTail(uint64_t epoch,
    const std::map<std::string, std::string>& meta,
    const std::string& name, uint64_t *position, bool next) {
  // fill in msg
  zlog_proto::MSeqRequest req;
  req.set_epoch(epoch);
  req.set_name(name);
  req.set_next(next);
  for (auto e : meta) {
    auto sp = req.add_meta();
    sp->set_key(e.first);
    sp->set_val(e.second);
  }
  req.set_count(1);

  channel *chan = channels_[next_channel_++ % num_channels_];
  std::lock_guard<std::mutex> l(chan->lock_);

  // serialize header and protobuf message
  uint32_t msg_size = req.ByteSize();
  uint32_t be_msg_size = htonl(msg_size);
  uint32_t total_msg_size = msg_size + sizeof(be_msg_size);
  assert(total_msg_size <= sizeof(chan->buffer));

  // add header
  memcpy(chan->buffer, &be_msg_size, sizeof(be_msg_size));

  // add protobuf msg
  assert(req.IsInitialized());
  assert(req.SerializeToArray(chan->buffer + sizeof(be_msg_size), msg_size));

  // send
  boost::asio::write(chan->socket_, boost::asio::buffer(chan->buffer, total_msg_size));

  // get reply
  boost::asio::read(chan->socket_, boost::asio::buffer(&be_msg_size, sizeof(be_msg_size)));
  msg_size = ntohl(be_msg_size);
  assert(msg_size < sizeof(chan->buffer));
  boost::asio::read(chan->socket_, boost::asio::buffer(chan->buffer, msg_size));

  // deserialize
  zlog_proto::MSeqReply reply;
  assert(reply.ParseFromArray(chan->buffer, msg_size));
  assert(reply.IsInitialized());

  if (reply.status() == zlog_proto::MSeqReply::INIT_LOG)
    return -EAGAIN;
  else if (reply.status() == zlog_proto::MSeqReply::STALE_EPOCH)
    return -ERANGE;
  else {
    assert(reply.status() == zlog_proto::MSeqReply::OK);
    assert(reply.position_size() == 1);
    *position = reply.position(0);
  }

  return 0;
}

int SeqrClient::CheckTail(uint64_t epoch,
    const std::map<std::string, std::string>& meta,
    const std::string& name, const std::set<uint64_t>& stream_ids,
    std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
    uint64_t *pposition, bool next)
{
  if (stream_ids.size() == 0)
    return -EINVAL;

  // fill in msg
  zlog_proto::MSeqRequest req;
  req.set_epoch(epoch);
  req.set_name(name);
  for (auto e : meta) {
    auto sp = req.add_meta();
    sp->set_key(e.first);
    sp->set_val(e.second);
  }
  req.set_next(next);
  req.set_count(1);
  for (std::set<uint64_t>::const_iterator it = stream_ids.begin();
       it != stream_ids.end(); it++) {
    uint64_t pos = *it;
    req.add_stream_ids(pos);
  }

  channel *chan = channels_[next_channel_++ % num_channels_];
  std::lock_guard<std::mutex> l(chan->lock_);

  // serialize header and protobuf message
  uint32_t msg_size = req.ByteSize();
  uint32_t be_msg_size = htonl(msg_size);
  uint32_t total_msg_size = msg_size + sizeof(be_msg_size);
  assert(total_msg_size <= sizeof(chan->buffer));

  // add header
  memcpy(chan->buffer, &be_msg_size, sizeof(be_msg_size));

  // add protobuf msg
  assert(req.IsInitialized());
  assert(req.SerializeToArray(chan->buffer + sizeof(be_msg_size), msg_size));

  // send
  boost::asio::write(chan->socket_, boost::asio::buffer(chan->buffer, total_msg_size));

  // get reply
  boost::asio::read(chan->socket_, boost::asio::buffer(&be_msg_size, sizeof(be_msg_size)));
  msg_size = ntohl(be_msg_size);
  assert(msg_size < sizeof(chan->buffer));
  boost::asio::read(chan->socket_, boost::asio::buffer(chan->buffer, msg_size));

  // deserialize
  zlog_proto::MSeqReply reply;
  assert(reply.ParseFromArray(chan->buffer, msg_size));
  assert(reply.IsInitialized());

  if (reply.status() == zlog_proto::MSeqReply::INIT_LOG)
    return -EAGAIN;
  else if (reply.status() == zlog_proto::MSeqReply::STALE_EPOCH)
    return -ERANGE;
  else {
    assert(reply.status() == zlog_proto::MSeqReply::OK);
    assert((unsigned)reply.stream_backpointers_size() == stream_ids.size());
    assert(reply.position_size() == 1);

    std::map<uint64_t, std::vector<uint64_t>> result;
    for (size_t index = 0; index < (unsigned)reply.stream_backpointers_size(); index++) {
      const zlog_proto::StreamBackPointer ptrs = reply.stream_backpointers(index);
      assert(stream_ids.find(ptrs.id()) != stream_ids.end());
      std::vector<uint64_t> backpointers(ptrs.backpointer().begin(),
          ptrs.backpointer().end());
      assert(result.find(ptrs.id()) == result.end());
      result[ptrs.id()] = backpointers;
    }

    stream_backpointers.swap(result);

    if (pposition)
      *pposition = reply.position(0);
  }

  return 0;
}

}
