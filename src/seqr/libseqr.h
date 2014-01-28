#include <boost/asio.hpp>
#include "server.h"

class SeqrClient {
 public:
  SeqrClient(const char *host, const char *port) :
    socket_(io_service_), host_(host), port_(port)
  {}

  void Connect() {
    boost::asio::ip::tcp::resolver resolver(io_service_);
    boost::asio::ip::tcp::resolver::query query(
        boost::asio::ip::tcp::v4(), host_.c_str(), port_);
    boost::asio::ip::tcp::resolver::iterator iterator = resolver.resolve(query);
    boost::asio::connect(socket_, iterator);
  }

  uint64_t NextSequence() {
    uint32_t cmd = htonl(SEQR_CMD_NEXT);
    boost::asio::write(socket_, boost::asio::buffer(&cmd, sizeof(cmd)));

    uint64_t seq;
    boost::asio::read(socket_, boost::asio::buffer(&seq, sizeof(seq)));
    seq = ntohl(seq);

    return seq;
  }

 private:
  boost::asio::io_service io_service_;
  boost::asio::ip::tcp::socket socket_;
  std::string host_;
  std::string port_;
};
