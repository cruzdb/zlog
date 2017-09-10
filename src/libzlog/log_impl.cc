// TODO
//  - use async methods for seal/maxpos
//  - use condvar with batching for update view
//  - reoder methods in file
//  - check update view for erange in stream checktail
#include "log_impl.h"

#include <cerrno>
#include <condition_variable>
#include <iostream>
#include <mutex>
#include <sstream>
#include <string>
#include <vector>

#include "proto/zlog.pb.h"
#include "include/zlog/log.h"
#include "include/zlog/backend.h"

#include "stripe_history.h"

/*
 * We can use Ceph API to query and make some intelligent decisiosn about what
 * the stripe size should be at runtime. In any case logs are not created
 * programmatically where this is needed. They are created for instance with a
 * CLI tool, and in any case the width can be changed online.
 */
#define DEFAULT_STRIPE_SIZE 100

namespace zlog {

Log::~Log() {}

std::string LogImpl::metalog_oid_from_name(const std::string& name)
{
  std::stringstream ss;
  ss << name << ".meta";
  return ss.str();
}

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

  auto views = Striper::InitViewData(stripe_size);
  int ret = backend->CreateLog(name, views);
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

  LogImpl *impl = new LogImpl(backend, hoid, prefix);

  impl->name_ = name;
  impl->seqr = seqr;

  ret = impl->UpdateView();
  if (ret) {
    delete impl;
    return ret;
  }

  if (impl->striper.Empty()) {
    delete impl;
    return -EINVAL;
  }

  *logptr = impl;

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
    }
  }
}

int LogImpl::StripeWidth()
{
  return striper.GetCurrent().width;
}

#if 0
int LogImpl::SetStripeWidth(int width)
{
  /*
   * Get the current projection. We'll add the new striping width when we
   * propose the next projection/epoch.
   */
  uint64_t epoch;
  zlog_proto::MetaLog config;
  int ret = be->LatestProjection(metalog_oid_, &epoch, config);
  if (ret != Backend::ZLOG_OK) {
    std::cerr << "failed to get projection ret " << ret << std::endl;
    return ret;
  }

  StripeHistory hist;
  ret = hist.Deserialize(config);
  if (ret)
    return ret;
  assert(!hist.Empty());

  std::vector<std::string> objects;
  mapper_.LatestObjectSet(objects, hist);

  uint64_t max_position;
  ret = Seal(objects, epoch, &max_position);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  uint64_t next_epoch = epoch + 1;
  hist.AddStripe(max_position, next_epoch, width);
  const auto hist_data = hist.Serialize();

  /*
   * Propose the updated projection for the next epoch.
   */
  ret = be->SetProjection(metalog_oid_, next_epoch, hist_data);
  if (ret != Backend::ZLOG_OK) {
    std::cerr << "failed to set new epoch " << next_epoch
      << " ret " << ret << std::endl;
    return ret;
  }

  return 0;
}
#endif

// Construct a new epoch view with an identifical configuration to the current
// view and return the maximum position.
//
// TODO
//  - there are probably several scenarios in which we might want to retry cut
//  creation (as opposed to just returning an error) if we encounter an error
//  that is resulting from races with other clients.
//  - the epoch return value seems weird.
//
int LogImpl::CreateCut(uint64_t *pepoch, uint64_t *pmaxpos)
{
  // make sure we are up-to-date
  int ret = UpdateView();
  if (ret)
    return ret;

  // get current configuration
  auto conf = striper.StripeObjects();
  auto epoch = conf.first;
  auto oids = conf.second;

  bool empty;
  uint64_t max_position;
  auto next_epoch = epoch + 1;
  ret = Seal(oids, next_epoch, &max_position, &empty);
  if (ret) {
    std::cerr << "failed to seal " << ret << std::endl;
    return ret;
  }

  std::string data;
  if (empty) {
    data = striper.NewResumeViewData();
  } else {
    data = striper.NewViewData(max_position + 1);
  }

  ret = be->ProposeView(hoid, next_epoch, data);
  if (ret)
    return ret;

  ret = UpdateView();
  if (ret)
    return ret;

  auto info = striper.GetCurrent();
  if (info.epoch < next_epoch)
    return -EINVAL;

  *pepoch = info.epoch;
  *pmaxpos = info.maxpos;

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

int LogImpl::CheckTail(uint64_t *pposition, bool increment)
{
  for (;;) {
    int ret = seqr->CheckTail(striper.Epoch(), be->pool(),
        name_, pposition, increment);
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

int LogImpl::CheckTail(uint64_t *pposition)
{
  return CheckTail(pposition, false);
}

int LogImpl::CheckTail(std::vector<uint64_t>& positions, size_t count)
{
  if (count <= 0 || count > 100)
    return -EINVAL;

  for (;;) {
    std::vector<uint64_t> result;
    int ret = seqr->CheckTail(striper.Epoch(), be->pool(),
        name_, result, count);
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
    int ret = seqr->CheckTail(striper.Epoch(), be->pool(),
        name_, stream_ids, stream_backpointers, pposition, increment);
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

}
