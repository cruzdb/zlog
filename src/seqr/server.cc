#include <cstdlib>
#include <iostream>
#include <boost/bind.hpp>
#include <boost/asio.hpp>
#include <boost/program_options.hpp>
#include "server.h"

namespace po = boost::program_options;

static uint64_t sequence;

class Session {
 public:
  Session(boost::asio::io_service& io_service)
    : socket_(io_service)
  {}

  boost::asio::ip::tcp::socket& socket() {
    return socket_;
  }

  void start() {
    boost::asio::async_read(socket_,
        boost::asio::buffer(buffer_, sizeof(uint32_t)),
        boost::bind(&Session::read_cmd, this,
          boost::asio::placeholders::error,
          boost::asio::placeholders::bytes_transferred));
  }

 private:
  void read_cmd(const boost::system::error_code& err, size_t size) {
    if (err) {
      delete this;
      return;
    }

    // boost guarantee
    assert(size == sizeof(uint32_t));

    uint32_t cmd = ntohl(*((uint32_t*)buffer_));
    switch (cmd) {
      case SEQR_CMD_CLOSE:
        delete this;
        return;

      case SEQR_CMD_NEXT:
      {
        uint64_t next = htonl(++sequence);
        boost::asio::async_write(socket_,
            boost::asio::buffer(&next, sizeof(next)),
            boost::bind(&Session::handle_write, this,
              boost::asio::placeholders::error,
              boost::asio::placeholders::bytes_transferred));
        break;
      }

      default:
        std::cerr << "restarting.." << std::endl;
        start();
    }
  }

  void handle_write(const boost::system::error_code& err, size_t size) {
    if (err) {
      delete this;
      return;
    }

    start();
  }

  boost::asio::ip::tcp::socket socket_;
  char buffer_[1024];
};

class Server {
 public:
  Server(boost::asio::io_service& io_service, short port)
    : io_service_(io_service),
    acceptor_(io_service,
        boost::asio::ip::tcp::endpoint(
          boost::asio::ip::tcp::v4(), port))
  {
    start_accept();
  }

 private:
  void start_accept() {
    Session* new_session = new Session(io_service_);
    acceptor_.async_accept(new_session->socket(),
        boost::bind(&Server::handle_accept, this, new_session,
          boost::asio::placeholders::error));
  }

  void handle_accept(Session* new_session,
      const boost::system::error_code& error) {
    if (!error)
      new_session->start();
    else
      delete new_session;
    start_accept();
  }

  boost::asio::io_service& io_service_;
  boost::asio::ip::tcp::acceptor acceptor_;
};

int main(int argc, char* argv[])
{
  int port;
  std::string host;

  po::options_description desc("Allowed options");
  desc.add_options()
    ("port", po::value<int>(&port)->required(), "Server port")
    ("daemon,d", "Run in background")
  ;

  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  po::notify(vm);

  boost::asio::io_service io_service;
  Server s(io_service, port);


  if (vm.count("daemon")) {
    io_service.notify_fork(boost::asio::io_service::fork_prepare);

    pid_t pid = fork();
    if (pid < 0) {
      exit(EXIT_FAILURE);
    }

    if (pid > 0) {
      exit(EXIT_SUCCESS);
    }

    pid_t sid = setsid();
    if (sid < 0) {
      exit(EXIT_FAILURE);
    }

    umask(0);

    close(0);
    close(1);
    close(2);

    io_service.notify_fork(boost::asio::io_service::fork_child);
  }

  io_service.run();

  return 0;
}
