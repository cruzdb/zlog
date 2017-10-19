#pragma once
#include <iostream>
#include <set>
#include <vector>
#include <mutex>
#include <atomic>
#include <boost/asio.hpp>

namespace zlog {

// it's important to delete any seqr clients that are created because when the
// channels are created in the constructor there are file descriptors created
// at that point (at least on OSX). When the derived class is the fake
// sequencer, we were just letting memory leak in tests... but it turns out that
// OSX will quickly reach an open file descriptor limit..
class SeqrClient {
 public:
  SeqrClient(const char *host, const char *port, uint64_t epoch) :
    host_(host), port_(port), epoch_(epoch)
  {
    num_channels_ = 5;
    next_channel_ = 0;
    for (int i = 0; i < num_channels_; i++) {
      channels_.push_back(new channel);
    }
  }

  virtual ~SeqrClient() {
    for (channel *chan : channels_) {
      chan->io_service_.stop();
      chan->socket_.close();
      delete chan;
    }
  }

  virtual void Connect();

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, uint64_t *position, bool next);

  virtual int CheckTail(uint64_t epoch,
      const std::map<std::string, std::string>& meta,
      const std::string& name, const std::set<uint64_t>& stream_ids,
      std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
      uint64_t *position, bool next);

  uint64_t Epoch() const {
    return epoch_;
  }

 private:
  struct channel {
    channel() : socket_(io_service_) {}
    boost::asio::io_service io_service_;
    boost::asio::ip::tcp::socket socket_;
    char buffer[1024];
    std::mutex lock_;
  };

  std::vector<channel*> channels_;

  std::string host_;
  std::string port_;
  uint64_t epoch_;

  int num_channels_;
  std::atomic<int> next_channel_;
};

}
