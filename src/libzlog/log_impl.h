#pragma once
#include <condition_variable>
#include <list>
#include <mutex>
#include <thread>
#include <CivetServer.h>

#include "include/zlog/log.h"
#include "include/zlog/statistics.h"
#include "libseq/libseqr.h"
#include "include/zlog/backend.h"
#include "striper.h"

#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

typedef Backend *(*backend_allocate_t)(void);
typedef void (*backend_release_t)(Backend*);

class LogImpl : public Log {
 public:
  LogImpl(const LogImpl&) = delete;
  LogImpl(const LogImpl&&) = delete;
  LogImpl& operator=(const LogImpl&) = delete;
  LogImpl& operator=(const LogImpl&&) = delete;

  LogImpl(std::shared_ptr<Backend> backend,
      const std::string& name,
      const std::string& hoid,
      const std::string& prefix,
      const std::string& secret,
      const Options& opts) :
    shutdown(false),
    backend(backend),
    name(name),
    hoid(hoid),
    prefix(prefix),
    striper(this, secret),
    options(opts)
#ifdef WITH_STATS
    ,metrics_http_server_(nullptr),
    metrics_handler_(this)
#endif
  {
#ifdef WITH_STATS
    if (!opts.http.empty()) {
      metrics_http_server_ = new CivetServer(opts.http);
      metrics_http_server_->addHandler("/metrics", &metrics_handler_);
    }
#endif
    assert(!name.empty());
    assert(!hoid.empty());
    assert(!prefix.empty());
  }

  ~LogImpl();

 public:
  int CheckTail(uint64_t *pposition) override;
  int CheckTail(uint64_t *pposition, bool increment);

 public:
  int Read(uint64_t position, std::string *data) override;
  int Append(const Slice& data, uint64_t *pposition) override;
  int Fill(uint64_t position) override;
  int Trim(uint64_t position) override;

 public:
  int AioRead(uint64_t position, zlog::AioCompletion *c,
      std::string *datap) override;

  int AioAppend(zlog::AioCompletion *c, const Slice& data,
      uint64_t *pposition) override;

 public:
  int StripeWidth() override {
    assert(0);
    // FIXME
    return -EINVAL;
  }

#ifdef WITH_STATS
 private:
  class MetricsHandler : public CivetHandler {
   public:
    explicit MetricsHandler(LogImpl* log) : log_(log) {}

    bool handleGet(CivetServer *server, struct mg_connection *conn) {

      auto stats = log_->options.statistics;

      std::stringstream out_stream;

      out_stream << stats->ToString() << std::endl;

      std::string body = out_stream.str();
      std::string content_type = "text/plain";

      mg_printf(conn,
          "HTTP/1.1 200 OK\r\n"
          "Content-Type: %s\r\n",
          content_type.c_str());

      mg_printf(conn, "Content-Length: %lu\r\n\r\n",
          static_cast<unsigned long>(body.size()));

      mg_write(conn, body.data(), body.size());

      return true;
    }

    LogImpl* log_;
  };
#endif

 public:
  bool shutdown;
  std::mutex lock;

  // thread-safe
  const std::shared_ptr<Backend> backend;

  const std::string name;
  const std::string hoid;
  const std::string prefix;

  Striper striper;

  std::string exclusive_cookie;
  uint64_t exclusive_position;
  bool exclusive_empty;

  const Options options;
#ifdef WITH_STATS
  CivetServer* metrics_http_server_ = nullptr;
  MetricsHandler metrics_handler_;
#endif
};

}
