#include "log_impl.h"

#include <cerrno>
#include <condition_variable>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <vector>
#include <boost/asio/ip/host_name.hpp>
#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>

#include "proto/zlog.pb.h"
#include "include/zlog/log.h"
#include "include/zlog/backend.h"

#include "fakeseqr.h"
#include "striper.h"

namespace zlog {

Log::~Log() {}

int Log::CreateWithStripeWidth(Backend *backend, const std::string& name,
    SeqrClient *seqr, int stripe_size, Log **logptr)
{
  if (stripe_size <= 0) {
    std::cerr << "Invalid stripe size (" << stripe_size << " <= 0)" << std::endl;
    return -EINVAL;
  }

  if (name.length() == 0) {
    std::cerr << "Invalid log name (empty string)" << std::endl;
    return -EINVAL;
  }

  // build initialization view blob
  auto init_view = Striper::InitViewData(stripe_size);
  std::string init_view_data;
  assert(init_view.SerializeToString(&init_view_data));

  int ret = backend->CreateLog(name, init_view_data);
  if (ret) {
    std::cerr << "Failed to create log " << name << " ret "
      << ret << " (" << strerror(-ret) << ")" << std::endl;
    return ret;
  }

  return Open(backend, name, seqr, logptr);
}

int Log::Create(Backend *backend, const std::string& name,
    SeqrClient *seqr, Log **logptr)
{
  return CreateWithStripeWidth(backend, name, seqr, DEFAULT_STRIPE_SIZE, logptr);
}

int Log::Open(Backend *backend, const std::string& name,
    SeqrClient *seqr, Log **logptr)
{
  if (name.empty())
    return -EINVAL;

  std::string hoid;
  std::string prefix;
  int ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    return ret;
  }

  auto impl = std::unique_ptr<LogImpl>(
      new LogImpl(backend, seqr, name, hoid, prefix));

  // shared/exclusive mode not yet set, so this may result in an invalid
  // sequencer configuration. that's ok, just make sure its all correct before
  // we go live.
  ret = impl->UpdateView();
  if (ret) {
    return ret;
  }

  if (impl->striper.Empty()) {
    return -EINVAL;
  }

  // exclusive/shared mode is chosen on start-up. as a result a client may exit
  // if the log mode is changed by a different client. TODO: dynamically
  // adjusting to these scenarios is future work.
  if (seqr) {
    ret = impl->ProposeSharedMode();
    if (ret)
      return ret;
  } else {
    ret = impl->ProposeExclusiveMode();
    if (ret)
      return ret;
  }

  *logptr = impl.release();

  return 0;
}

int LogImpl::UpdateView()
{
  // striper initialized from epoch 0
  uint64_t epoch = striper.Empty() ? 0 : striper.Epoch() + 1;

  while (true) {
    std::map<uint64_t, std::string> views;
    int ret = be->ReadViews(hoid, epoch, views);
    if (ret)
      return ret;
    if (views.empty())
      return 0;
    for (auto it = views.begin(); it != views.end(); it++) {
      if (it->first != epoch) {
        // gap: bad...
        return -EIO;
      }
      striper.Add(it->first, it->second);
      epoch++;

      auto view = striper.LatestView();
      if (exclusive_cookie.empty()) {                        // log wants shared mode
        if (view.has_exclusive_cookie()) {                   // view is exclusive mode (BAD)
          assert(!view.exclusive_cookie().empty());
          active_seqr = nullptr;
        } else {                                             // view is shared mode (GOOD)
          active_seqr = shared_seqr;
        }
      } else {                                               // log wants exclusive mode
        if (view.has_exclusive_cookie()) {                   // view is exclusive mode (GOOD)
          assert(!view.exclusive_cookie().empty());
          if (view.exclusive_cookie() == exclusive_cookie) { // cookie match (GOOD)
            auto client = std::unique_ptr<FakeSeqrClient>(
                new FakeSeqrClient(be->pool(), name,
                  exclusive_empty, exclusive_position));
            active_seqr = client.release();
            // TODO: we don't do anything to clean-up the sequencers so this is
            // a memory leak. Currently the sequencer state needs to remain
            // unchanged since instantiation. We'll take care of the leak when
            // we add more robust sequencer switching.
          } else {                                           // cookie no match (BAD)
            active_seqr = nullptr;
          }
        } else {                                             // view is shared mode (BAD)
          active_seqr = nullptr;
        }
      }
    }
  }
}

// generate a new view, but do not propose it.
int LogImpl::CreateNextView(uint64_t *pepoch, uint64_t *pmaxpos, bool *pempty,
    zlog_proto::View& view)
{
  int ret = UpdateView();
  if (ret)
    return ret;

  auto conf = striper.GetCurrent();

  bool empty;
  uint64_t max_position;
  auto next_epoch = conf.epoch + 1;
  ret = Seal(conf.oids, next_epoch, &max_position, &empty);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  // if the latest stripe is empty, it may also mean that the entire log is
  // empty. the output parameters correspond to max/empty of the log, not the
  // current stripe.
  uint64_t out_maxpos;
  bool out_empty;
  view = striper.LatestView();
  if (empty) {
    if (conf.minpos == 0) {
      // the log is empty, so out_maxpos is undefined.
      out_empty = true;
    } else {
      out_empty = false;
      out_maxpos = conf.minpos - 1;
    }
  } else {
    out_maxpos = max_position;
    out_empty = false;
    // next stripe starts with _next_ position: current max + 1
    view.set_position(max_position + 1);
  }

  if (pepoch)
    *pepoch = next_epoch;
  if (pempty)
    *pempty = out_empty;
  if (!out_empty && pmaxpos)
    *pmaxpos = out_maxpos;

  return 0;
}

int LogImpl::ProposeNextView(uint64_t next_epoch,
    const zlog_proto::View& view)
{
  std::string view_data;
  assert(view.SerializeToString(&view_data));

  int ret = be->ProposeView(hoid, next_epoch, view_data);
  if (ret)
    return ret;

  ret = UpdateView();
  if (ret)
    return ret;

  /*
   * TODO: this check may be overly strict, and it may be the case that we want
   * to retry in different scenarios (e.g. re-populate sequencer state vs
   * changing the stripe configuration).
   */
  if (striper.GetCurrent().epoch != next_epoch)
    return -EINVAL;

  return 0;
}

int LogImpl::CreateCut(uint64_t *pepoch, uint64_t *pmaxpos, bool *pempty)
{
  uint64_t next_epoch;
  zlog_proto::View view;
  int ret = CreateNextView(&next_epoch, pmaxpos, pempty, view);
  if (ret)
    return ret;

  ret = ProposeNextView(next_epoch, view);
  if (ret)
    return ret;

  if (pepoch)
    *pepoch = next_epoch;

  return 0;
}

int LogImpl::Seal(const std::vector<std::string>& objects,
    uint64_t epoch, uint64_t *pmaxpos, bool *pempty)
{
  // seal objects
  for (auto oid : objects) {
    int ret = be->Seal(oid, epoch);
    if (ret) {
      std::cerr << "failed to seal object" << std::endl;
      return ret;
    }
  }

  // query objects for max pos
  uint64_t max_position;
  bool initialized = false;
  for (auto oid : objects) {
    bool empty;
    uint64_t pos;
    int ret = be->MaxPos(oid, epoch, &pos, &empty);
    if (ret) {
      std::cerr << "failed to find max pos ret " << ret << std::endl;
      return ret;
    }

    if (!empty && !initialized) {
      max_position = pos;
      initialized = true;
      continue;
    }

    max_position = std::max(max_position, pos);
  }

  *pempty = !initialized;
  if (initialized)
    *pmaxpos = max_position;

  return 0;
}

int LogImpl::ProposeSharedMode()
{
  uint64_t next_epoch;
  zlog_proto::View view;
  int ret = CreateNextView(&next_epoch, NULL, NULL, view);
  if (ret)
    return ret;

  assert(!view.has_exclusive_cookie());
  assert(exclusive_cookie.empty());

  return ProposeNextView(next_epoch, view);
}

int LogImpl::ProposeExclusiveMode()
{
  bool empty;
  uint64_t position;
  uint64_t next_epoch;
  zlog_proto::View view;
  int ret = CreateNextView(&next_epoch, &position, &empty, view);
  if (ret)
    return ret;

  // generate the exclusive cookie. a unique value is guaranteed by encoding
  // next_epoch which will be unique if the new view is accepted.
  auto uuid = boost::uuids::random_generator()();
  auto hostname = boost::asio::ip::host_name();
  std::stringstream exclusive_cookie_ss;
  exclusive_cookie_ss << uuid << "." << hostname
    << "." << next_epoch;
  const auto cookie = exclusive_cookie_ss.str();

  // make sure that exclusive_cookie is set before calling ProposeNextView so
  // that when UpdateView is called it will pick up the new mode.
  exclusive_cookie = cookie;
  view.set_exclusive_cookie(cookie);

  // used in UpdateView to construct the fake sequencer instance.
  exclusive_empty = empty;
  exclusive_position = position;

  return ProposeNextView(next_epoch, view);
}

int LogImpl::CheckTail(uint64_t *pposition)
{
  return CheckTail(pposition, false);
}

int LogImpl::CheckTail(uint64_t *pposition, bool increment)
{
  for (;;) {
    if (!active_seqr) {
      std::cerr << "no active sequencer" << std::endl;
      return -EINVAL;
    }
    int ret = active_seqr->CheckTail(striper.Epoch(), be->pool(),
        name, pposition, increment);
    if (ret == -EAGAIN) {
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = UpdateView();
      if (ret)
        return ret;
      continue;
    }
    return ret;
  }
  assert(0);
  return -EIO;
}

int LogImpl::CheckTail(std::vector<uint64_t>& positions, size_t count)
{
  if (count <= 0 || count > 100)
    return -EINVAL;

  for (;;) {
    std::vector<uint64_t> result;
    if (!active_seqr) {
      std::cerr << "no active sequencer" << std::endl;
      return -EINVAL;
    }
    int ret = active_seqr->CheckTail(striper.Epoch(), be->pool(),
        name, result, count);
    if (ret == -EAGAIN) {
      //std::cerr << "check tail ret -ESPIPE" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      //std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = UpdateView();
      if (ret)
        return ret;
      continue;
    }
    if (ret == 0)
      positions.swap(result);
    return ret;
  }
  assert(0);
  return -EIO;
}

int LogImpl::CheckTail(const std::set<uint64_t>& stream_ids,
    std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
    uint64_t *pposition, bool increment)
{
  for (;;) {
    if (!active_seqr) {
      std::cerr << "no active sequencer" << std::endl;
      return -EINVAL;
    }
    int ret = active_seqr->CheckTail(striper.Epoch(), be->pool(),
        name, stream_ids, stream_backpointers, pposition, increment);
    if (ret == -EAGAIN) {
      //std::cerr << "check tail ret -ESPIPE" << std::endl;
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
      //std::cerr << "check tail ret -ERANGE" << std::endl;
      ret = UpdateView();
      if (ret)
        return ret;
      continue;
    }
    return ret;
  }
  assert(0);
  return -EIO;
}

int LogImpl::Read(uint64_t position, std::string *data)
{
  for (;;) {
    auto mapping = striper.MapPosition(position);

    int ret = be->Read(mapping.oid, mapping.epoch, position, data);
    switch (ret) {
      case 0:
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      case -ENOENT:  // not-written
      case -ENODATA: // invalidated
      default:
        return ret;
    }
  }
  assert(0);
  return -EIO;
}

int LogImpl::Read(uint64_t epoch, uint64_t position, std::string *data)
{
  for (;;) {
    auto mapping = striper.MapPosition(position);

    int ret = be->Read(mapping.oid, epoch, position, data);
    switch (ret) {
      case 0:
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      case -ENOENT:  // not-written
      case -ENODATA: // invalidated
      default:
        return ret;
    }
  }
  assert(0);
  return -EIO;
}

int LogImpl::Append(const Slice& data, uint64_t *pposition)
{
  for (;;) {
    uint64_t position;
    int ret = CheckTail(&position, true);
    if (ret)
      return ret;

    auto mapping = striper.MapPosition(position);

    ret = be->Write(mapping.oid, data, mapping.epoch, position);
    switch (ret) {
      case 0:
        if (pposition)
          *pposition = position;
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      case -EROFS:
        continue;

      default:
        return ret;
    }
  }
  assert(0);
  return -EIO;
}

int LogImpl::Fill(uint64_t position)
{
  for (;;) {
    auto mapping = striper.MapPosition(position);

    int ret = be->Fill(mapping.oid, mapping.epoch, position);
    switch (ret) {
      case 0:
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      case -EROFS:
      default:
        return ret;
    }
  }
}

int LogImpl::Fill(uint64_t epoch, uint64_t position)
{
  for (;;) {
    auto mapping = striper.MapPosition(position);

    int ret = be->Fill(mapping.oid, epoch, position);
    switch (ret) {
      case 0:
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      case -EROFS:
      default:
        return ret;
    }
  }
}

int LogImpl::Trim(uint64_t position)
{
  for (;;) {
    auto mapping = striper.MapPosition(position);

    int ret = be->Trim(mapping.oid, mapping.epoch, position);
    switch (ret) {
      case 0:
        return 0;

      case -ESPIPE:
        ret = UpdateView();
        if (ret)
          return ret;
        sleep(1);
        continue;

      default:
        return ret;
    }
  }
}

}
