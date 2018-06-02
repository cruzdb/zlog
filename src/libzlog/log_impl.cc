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
#include <dlfcn.h>
#include <stdlib.h>

#include "proto/zlog.pb.h"
#include "include/zlog/log.h"
#include "include/zlog/backend.h"

#include "fakeseqr.h"
#include "striper.h"

namespace zlog {

int LogImpl::Open(const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts, LogImpl **logpp,
    std::shared_ptr<Backend> *out_backend)
{
  std::shared_ptr<Backend> backend;
  int ret = Backend::Load(scheme, opts, backend);
  if (ret)
    return ret;

  if (out_backend)
    *out_backend = backend;

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    std::cerr << "failed to open log backend " << ret << std::endl;
    return ret;
  }

  Options options;

  auto log = std::unique_ptr<zlog::LogImpl>(
      new zlog::LogImpl(backend, name, hoid, prefix, options));

  ret = log->UpdateView();
  if (ret) {
    return ret;
  }

  if (log->striper.Empty()) {
    return -EINVAL;
  }

  *logpp = log.release();

  return 0;
}

LogImpl::~LogImpl()
{
  {
    std::lock_guard<std::mutex> l(lock);
    shutdown = true;
  }
  view_update.notify_one();
  view_update_thread.join();

  metrics_http_server_.removeHandler("/metrics");
  metrics_http_server_.close();

}

int LogImpl::UpdateView()
{
  std::unique_lock<std::mutex> lk(lock);

  bool done = false;
  std::condition_variable cond;
  view_update_waiters.emplace_back(&cond, &done);

  view_update.notify_one();
  cond.wait(lk, [&done] { return done; });

  return 0;
}

void LogImpl::ViewUpdater()
{
  while (true) {
    {
      std::unique_lock<std::mutex> lk(lock);
      view_update.wait(lk, [&] {
          return !view_update_waiters.empty() || shutdown;
          });
      if (shutdown)
        break;
    }

    // striper initialized from epoch 0
    uint64_t epoch = striper.Empty() ? 0 : striper.Epoch() + 1;

    // query for new views since epoch
    std::map<uint64_t, std::string> views;
    int ret = backend->ReadViews(hoid, epoch, views);
    if (ret) {
      std::cerr << "read views error " << ret << std::endl;
      continue;
    }

    // no updates found
    if (views.empty()) {
      std::lock_guard<std::mutex> lk(lock);
      for (auto w : view_update_waiters) {
        w.first->notify_one();
        *w.second = true;
      }
      view_update_waiters.clear();
      continue;
    }

    // apply updates. we are going to apply all the updates, but not build a new
    // sequencer until all updates are applied. if a client uses a sequencer
    // tagged with an older epoch, then they will notice and retry. the race is
    // safe, and very narrow.
    for (auto it = views.begin(); it != views.end(); it++) {
      if (it->first != epoch) {
        std::cerr << "view gap found. very bad." << std::endl;
        assert(0);
        exit(0);
        return;
      }
      ret = striper.Add(it->first, it->second);
      if (ret) {
        std::cerr << "failed to add view" << std::endl;
        exit(1);
        return;
      }
      epoch++;
    }

    /*
     * build a sequencer based on the latest view. the semantics of creating and
     * opening logs, with and without sequencers or in exclusive mode, combined
     * with the behavior when the log is already opened by other clients... is
     * confusing. right now the approach is to always try to keep the log open.
     * the only time we can't keep the log open is when transitioning to an
     * exclusive mode without the proper token.
     */
    std::shared_ptr<SeqrClient> client;
    auto view = striper.LatestView();
    if (view.second.has_exclusive_cookie()) {
      assert(!view.second.exclusive_cookie().empty());
      if (view.second.exclusive_cookie() == exclusive_cookie) {
        client = std::make_shared<FakeSeqrClient>(backend->meta(), name,
            exclusive_empty, exclusive_position, view.first);
      }
    } else {
      if (view.second.has_host() && view.second.has_port()) {
        client = std::make_shared<zlog::SeqrClient>(view.second.host().c_str(),
            view.second.port().c_str(), view.first);
      } else {
        std::cerr << "no host and port found" << std::endl;
      }
    }

    if (client)
      client->Connect();

    std::lock_guard<std::mutex> lk(lock);

    sequencer = client;
  }
  std::lock_guard<std::mutex> lk(lock);
  assert(view_update_waiters.empty());
}

// generate a new view, but do not propose it.
//
// TODO
//   - with fixed number of entries per stripe, we have two different types of
//   sealing. when creating a normal view to extend the current one, we really
//   don't need to seal any objects. we only need to seal when mappings are
//   going to _change_
//   - CURRENTLY we create strictly disjoint views that are abutt. so we
//   actually don't care what the current maximum position is in a stripe when
//   sealing---if the stripe isn't full, the mappings to that stripe will still
//   remain valid. however, when we start to allow stripes to be sealed shut
//   before they are full, we actually will care about the max position.
//   - when sealing to trim current stripe, watch out for multiple empty stripes
//   being present and what that might mean for calculating the max pos.
//
//   - Need to figure out what extending means for sealing and seqr recovery.
//   this actually probably works correctly now. but if there were very little
//   positions haveing been written, but lots of extended views, then the seal
//   process would create a giant hole. the sequencer woudl start handing out
//   positions at the end. but... we can optimize that later.
int LogImpl::CreateNextView(uint64_t *pepoch, uint64_t *pmaxpos, bool *pempty,
    zlog_proto::View& view, bool extend)
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
  uint64_t out_maxpos = 0; // initialization is ONLY for -Werror=maybe-uninitialized
  bool out_empty;
  view = striper.LatestView().second; // start with a copy of the current view
  if (extend) {
    out_empty = false; // squash uninit use warning
    assert(!pempty);
    assert(!pmaxpos);
    uint64_t next_pos = view.position() +
      (view.width() * view.entries_per_object());
    view.set_position(next_pos);
  } else if (empty) {
    if (conf.minpos == 0) {
      // the log is empty, so out_maxpos is undefined.
      // view will have the same configuration, newer epoch
      out_empty = true;
    } else {
      assert(conf.minpos > 0);
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
  if (!view.SerializeToString(&view_data)) {
    std::cerr << "invalid proto" << std::endl << std::flush;
    exit(1);
    return -EINVAL;
  }

  int ret = backend->ProposeView(hoid, next_epoch, view_data);
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

// Want to seal to get accurate maximum, but we don't really want to change any
// mappings. we just need everyone to stop so the sequencer can initialize its
// state.
int LogImpl::CreateCut(uint64_t *pepoch, uint64_t *pmaxpos, bool *pempty, bool extend)
{
  uint64_t next_epoch;
  zlog_proto::View view;
  int ret = CreateNextView(&next_epoch, pmaxpos, pempty, view, extend);
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
    int ret = backend->Seal(oid, epoch);
    if (ret) {
      std::cerr << "failed to seal object" << std::endl;
      return ret;
    }
  }

  // query objects for max pos
  uint64_t max_position = 0; // initialization is ONLY for -Werror=maybe-uninitialized
  bool initialized = false;
  for (auto oid : objects) {
    bool empty;
    uint64_t pos;
    int ret = backend->MaxPos(oid, epoch, &pos, &empty);
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

// TODO: in order extend we use create cut which seals the current stripe.
// really we want to extend the stripe without sealing. this is ok, we just need
// to change the way we build the view map. later...
//
// TODO: if the current view is empty, create cut doesn't extend it. if a
// sequencer hands out a bunch of positions that span the next view, but that
// view hasn't been craeted yet AND the current view is empty which could happen
// with a race, extend map will just keep duplicating the current map. this
// happened with the Fill unit test that starts off appending to a position in
// the next view. So we need to add a mode so that create cut will extend the
// map.
//
// TODO: we also don't need to seal for extension
int LogImpl::ExtendMap()
{
  std::cout << "extending map" << std::endl;
  return CreateCut(nullptr, nullptr, nullptr, true);
}

int LogImpl::CheckTail(uint64_t *pposition)
{
  return CheckTail(pposition, nullptr, false);
}

int LogImpl::CheckTail(uint64_t *pposition, uint64_t *epoch,
    bool increment)
{
  while (true) {
    std::unique_lock<std::mutex> l(lock);
    auto seq = sequencer;
    l.unlock();

    if (!seq) {
      std::cerr << "no active sequencer" << std::endl;
      return -EINVAL;
    }

    int ret = seq->CheckTail(striper.Epoch(), backend->meta(),
        name, pposition, increment);
    if (!ret) {
      if (epoch)
        *epoch = seq->Epoch();
      return 0;
    } else if (ret == -EAGAIN) {
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

#ifdef STREAMING_SUPPORT
int LogImpl::CheckTail(const std::set<uint64_t>& stream_ids,
    std::map<uint64_t, std::vector<uint64_t>>& stream_backpointers,
    uint64_t *pposition, bool increment)
{
  for (;;) {
    std::unique_lock<std::mutex> l(lock);
    auto seq = sequencer;
    l.unlock();

    if (!seq) {
      std::cerr << "no active sequencer" << std::endl;
      return -EINVAL;
    }

    int ret = seq->CheckTail(striper.Epoch(), backend->meta(),
        name, stream_ids, stream_backpointers, pposition, increment);
    if (ret == -EAGAIN) {
      sleep(1);
      continue;
    } else if (ret == -ERANGE) {
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
#endif

int LogImpl::Read(uint64_t position, std::string *data)
{
  while (true) {
    auto mapping = striper.MapPosition(position);
    if (!mapping) {
      int ret = ExtendMap();
      if (ret < 0)
        return ret;
      continue;
    }
    int ret = backend->Read(mapping->oid, mapping->epoch, position,
        mapping->width, mapping->max_size, data);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
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

#ifdef STREAMING_SUPPORT
int LogImpl::Read(uint64_t epoch, uint64_t position, std::string *data)
{
  while (true) {
    auto mapping = striper.MapPosition(position);
    int ret = backend->Read(mapping.oid, epoch, position, data);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
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
#endif

int LogImpl::Append(const Slice& data, uint64_t *pposition)
{
  while (true) {
    // contact the sequencer for the append position. the latest epoch at which
    // the sequencer instance is valid is returned.
    uint64_t seq_epoch;
    uint64_t position;
    int ret = CheckTail(&position, &seq_epoch, true);
    if (ret)
      return ret;

    // map the position from the sequencer to a storage object. if the epoch has
    // changed, it may mean the sequencer changed, so we behave conservatively
    // and retry. note that one could optimize this case and check only that the
    // sequencer was invalidated even if the view changed.
    auto mapping = striper.MapPosition(position);
    while (!mapping) {
      ret = ExtendMap();
      if (ret < 0)
        return ret;
      mapping = striper.MapPosition(position);
    }

    if (seq_epoch != mapping->epoch) {
      std::cerr << "retry with new seq" << std::endl;
      continue;
    }

    ret = backend->Write(mapping->oid, data, mapping->epoch, position,
        mapping->width, mapping->max_size);
    if (!ret) {
      if (pposition)
        *pposition = position;
      return 0;
    }

    if (ret == -ESPIPE) {
      ret = UpdateView();
      if (ret)
        return ret;
      continue;
    }

    if (ret == -EROFS)
      continue;

    return ret;
  }
  assert(0);
  return -EIO;
}

int LogImpl::Fill(uint64_t position)
{
  while (true) {
    auto mapping = striper.MapPosition(position);
    if (!mapping) {
      int ret = ExtendMap();
      if (ret < 0)
        return ret;
      continue;
    }

    int ret = backend->Fill(mapping->oid, mapping->epoch, position,
        mapping->width, mapping->max_size);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
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

#ifdef STREAMING_SUPPORT
int LogImpl::Fill(uint64_t epoch, uint64_t position)
{
  while (true) {
    auto mapping = striper.MapPosition(position);
    int ret = backend->Fill(mapping.oid, epoch, position);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
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
#endif

int LogImpl::Trim(uint64_t position)
{
  while (true) {
    auto mapping = striper.MapPosition(position);
    if (!mapping) {
      int ret = ExtendMap();
      if (ret < 0)
        return ret;
      continue;
    }

    int ret = backend->Trim(mapping->oid, mapping->epoch, position,
        mapping->width, mapping->max_size);
    if (!ret)
      return 0;
    if (ret == -ESPIPE) {
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

}
