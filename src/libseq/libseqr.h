#ifndef LIBSEQR_H
#define LIBSEQR_H
#include <set>
#include <boost/asio.hpp>

namespace zlog {

class SeqrClient {
 public:
  SeqrClient(const char *host, const char *port) :
    socket_(io_service_), host_(host), port_(port)
  {}

  virtual void Connect();

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, uint64_t *position, bool next);

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, std::vector<uint64_t>& positions, size_t count);

  virtual int CheckTail(uint64_t epoch, const std::string& pool,
      const std::string& name, const std::set<uint64_t>& stream_ids,
      std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
      uint64_t *position, bool next);

 private:
  boost::asio::io_service io_service_;
  boost::asio::ip::tcp::socket socket_;
  std::string host_;
  std::string port_;
  char buffer[1024];
};

}

#endif
