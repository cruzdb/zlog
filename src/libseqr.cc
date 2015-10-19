#include <boost/asio.hpp>
#include "libseqr.h"
#include "zlog.pb.h"

namespace zlog {

void SeqrClient::Connect() {
  boost::asio::ip::tcp::resolver resolver(io_service_);
  boost::asio::ip::tcp::resolver::query query(
      boost::asio::ip::tcp::v4(), host_.c_str(), port_);
  boost::asio::ip::tcp::resolver::iterator iterator = resolver.resolve(query);
  socket_.connect(*iterator);
}

int SeqrClient::CheckTail(uint64_t epoch, const std::string& pool,
    const std::string& name, uint64_t *position, bool next) {
  // fill in msg
  zlog_proto::MSeqRequest req;
  req.set_epoch(epoch);
  req.set_name(name);
  req.set_next(next);
  req.set_pool(pool);
  req.set_count(1);

  // serialize header and protobuf message
  uint32_t msg_size = req.ByteSize();
  uint32_t be_msg_size = htonl(msg_size);
  uint32_t total_msg_size = msg_size + sizeof(be_msg_size);
  assert(total_msg_size <= sizeof(buffer));

  // add header
  memcpy(buffer, &be_msg_size, sizeof(be_msg_size));

  // add protobuf msg
  assert(req.IsInitialized());
  assert(req.SerializeToArray(buffer + sizeof(be_msg_size), msg_size));

  // send
  boost::asio::write(socket_, boost::asio::buffer(buffer, total_msg_size));

  // get reply
  boost::asio::read(socket_, boost::asio::buffer(&be_msg_size, sizeof(be_msg_size)));
  msg_size = ntohl(be_msg_size);
  assert(msg_size < sizeof(buffer));
  boost::asio::read(socket_, boost::asio::buffer(buffer, msg_size));

  // deserialize
  zlog_proto::MSeqReply reply;
  assert(reply.ParseFromArray(buffer, msg_size));
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

int SeqrClient::CheckTail(uint64_t epoch, const std::string& pool,
    const std::string& name, std::vector<uint64_t>& positions, size_t count)
{
  if (count <= 0 || count > 100)
    return -EINVAL;

  // fill in msg
  zlog_proto::MSeqRequest req;
  req.set_epoch(epoch);
  req.set_name(name);
  req.set_pool(pool);
  req.set_next(true);
  req.set_count(count);

  // serialize header and protobuf message
  uint32_t msg_size = req.ByteSize();
  uint32_t be_msg_size = htonl(msg_size);
  uint32_t total_msg_size = msg_size + sizeof(be_msg_size);
  assert(total_msg_size <= sizeof(buffer));

  // add header
  memcpy(buffer, &be_msg_size, sizeof(be_msg_size));

  // add protobuf msg
  assert(req.IsInitialized());
  assert(req.SerializeToArray(buffer + sizeof(be_msg_size), msg_size));

  // send
  boost::asio::write(socket_, boost::asio::buffer(buffer, total_msg_size));

  // get reply
  boost::asio::read(socket_, boost::asio::buffer(&be_msg_size, sizeof(be_msg_size)));
  msg_size = ntohl(be_msg_size);
  assert(msg_size < sizeof(buffer));
  boost::asio::read(socket_, boost::asio::buffer(buffer, msg_size));

  // deserialize
  zlog_proto::MSeqReply reply;
  assert(reply.ParseFromArray(buffer, msg_size));
  assert(reply.IsInitialized());

  if (reply.status() == zlog_proto::MSeqReply::INIT_LOG)
    return -EAGAIN;
  else if (reply.status() == zlog_proto::MSeqReply::STALE_EPOCH)
    return -ERANGE;
  else {
    assert(reply.status() == zlog_proto::MSeqReply::OK);
    std::vector<uint64_t> result(reply.position().begin(),
        reply.position().end());
    positions.swap(result);
  }

  return 0;
}

}
