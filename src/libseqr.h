#ifndef LIBSEQR_H
#define LIBSEQR_H
#include <boost/asio.hpp>

namespace zlog {

class SeqrClient {
 public:
  SeqrClient(const char *host, const char *port) :
    socket_(io_service_), host_(host), port_(port)
  {}

  void Connect();

  int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, uint64_t *position, bool next);

 private:
  boost::asio::io_service io_service_;
  boost::asio::ip::tcp::socket socket_;
  std::string host_;
  std::string port_;
  char buffer[1024];
};

}

#endif
