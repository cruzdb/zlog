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

/*
 * TODO: instead of passing these in as macros, we can put some of this shared
 * library code in a module and then use configure_file to do the substitution.
 */
#define BE_PREFIX CMAKE_SHARED_LIBRARY_PREFIX "zlog_backend_"
#define BE_SUFFIX CMAKE_SHARED_LIBRARY_SUFFIX

#define BE_ALLOCATE "__backend_allocate"
#define BE_RELEASE "__backend_release"

// TODO: wrap up this backend business in a resource all the callers have to
// carefully manage a bunch of return values right now.
int LogImpl::OpenBackend(const std::string& scheme,
    const std::map<std::string, std::string>& opts,
    void **hp, Backend **bpp, backend_release_t *rp,
    bool *extra_ref)
{
  bool do_extra_ref = false;
  if (extra_ref) {
    do_extra_ref = *extra_ref;
    *extra_ref = false;
  }

  // try system lib dir
  char path[PATH_MAX];
  int ret = snprintf(path, sizeof(path), "%s/" BE_PREFIX "%s" BE_SUFFIX,
      ZLOG_LIBDIR, scheme.c_str());
  if (ret >= (int)sizeof(path)) {
    return -ENAMETOOLONG;
  }

  auto handle = dlopen(path, RTLD_NOW);
  if (handle == nullptr) {
    // try $PWD/lib
    ret = snprintf(path, sizeof(path), "%s/" BE_PREFIX "%s" BE_SUFFIX,
        "lib", scheme.c_str());
    if (ret >= (int)sizeof(path)) {
      return -ENAMETOOLONG;
    }

    handle = dlopen(path, RTLD_NOW);
    if (handle == nullptr) {
      std::cerr << "could not load backend " << dlerror() << std::endl;
      return -EINVAL;
    }
  }

  if (do_extra_ref) {
    dlopen(path, RTLD_NOW);
    *extra_ref = true;
  }

  // technically the symbol value could be null in the module, rather than
  // indicating an error. this might be useful later. check the man page.
  auto allocate = (backend_allocate_t)dlsym(handle, BE_ALLOCATE);
  if (allocate == nullptr) {
    dlclose(handle);
    std::cerr << "could not find symbol " << dlerror() << std::endl;
    return -EINVAL;
  }

  auto release = (backend_release_t)dlsym(handle, BE_RELEASE);
  if (release == nullptr) {
    dlclose(handle);
    std::cerr << "could not find symbol " << dlerror() << std::endl;
    return -EINVAL;
  }

  auto backend = allocate();
  assert(backend);

  ret = backend->Initialize(opts);
  if (ret) {
    release(backend);
    dlclose(handle);
    return ret;
  }

  *hp = handle;
  *bpp = backend;
  *rp = release;

  return 0;
}

int LogImpl::Open(const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts, LogImpl **logpp,
    bool *extra_ref)
{
  void *handle;
  Backend *backend;
  backend_release_t release;

  int ret = LogImpl::OpenBackend(scheme, opts,
      &handle, &backend, &release, extra_ref);
  if (ret)
    return ret;

  std::string hoid;
  std::string prefix;
  ret = backend->OpenLog(name, hoid, prefix);
  if (ret) {
    std::cerr << "failed to open log backend " << ret << std::endl;
    release(backend);
    dlclose(handle);
    return ret;
  }

  auto log = std::unique_ptr<zlog::LogImpl>(
      new zlog::LogImpl(backend, nullptr, name, hoid, prefix));

  // handle/release now owned by log
  log->be_handle = handle;
  log->be_release = release;

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

int Log::Create(const std::string& scheme, const std::string& name,
    const std::map<std::string, std::string>& opts,
    SeqrClient *seqr, Log **logpp)
{
  void *handle;
  Backend *backend;
  backend_release_t release;

  int ret = LogImpl::OpenBackend(scheme, opts,
      &handle, &backend, &release, nullptr);
  if (ret)
    return ret;

  ret = Create(backend, name, seqr, logpp);
  if (ret) {
    release(backend);
    dlclose(handle);
    return ret;
  }

  // backend is now managed by the log instance
  ((LogImpl*)(*logpp))->be_handle = handle;
  ((LogImpl*)(*logpp))->be_release = release;

  return 0;
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

LogImpl::~LogImpl()
{
  if (active_seqr && active_seqr != shared_seqr)
    delete active_seqr;

  // backend owned by log instance?
  if (be_handle || be_release) {
    assert(be_handle && be_release);
    // release instance in backend module
    be_release(be);
    // release our reference on the module
    dlclose(const_cast<void*>(be_handle));
  }
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
                new FakeSeqrClient(be->meta(), name,
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
  uint64_t out_maxpos = 0; // initialization is ONLY for -Werror=maybe-uninitialized
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
  uint64_t max_position = 0; // initialization is ONLY for -Werror=maybe-uninitialized
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
    // TODO: the sequencer at this level of abstraction should not be exposing
    // pools and log names. It should just be a simple CheckTail interface. The
    // constructor can take care of the rest. For instance, it might be that a
    // connection implies certain metadata and we odn't need to send it. Or
    // maybe the sequener transparently adds this metadata from the configured
    // backend.
    int ret = active_seqr->CheckTail(striper.Epoch(), be->meta(),
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
    int ret = active_seqr->CheckTail(striper.Epoch(), be->meta(),
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
    int ret = active_seqr->CheckTail(striper.Epoch(), be->meta(),
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
