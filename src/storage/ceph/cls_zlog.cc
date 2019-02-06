#include "cls_zlog.h"

CLS_VER(1,0)
CLS_NAME(zlog)

static int log_entry_read(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::ReadEntryOp>(in);
  if (!op) {
    CLS_ERR("ERROR: log_entry_read(): failed to decode input");
    return -EINVAL;
  }

  cls_zlog::LogObjectHeader header(hctx);
  int ret = header.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_read(): failed to read header %d", ret);
    return ret;
  }

  ret = header.epoch_guard(op->epoch());
  if (ret < 0) {
    CLS_LOG(10, "log_entry_read(): failed epoch guard %d", ret);
    return ret;
  }

  if (header.position_trimmed(op->position())) {
    CLS_LOG(10, "log_entry_read(): position %llu in trim range",
        op->position());
    return -ENODATA;
  }

  cls_zlog::LogEntry entry(hctx, op->position());
  ret = entry.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_read(): error reading entry %d", ret);
    return ret;
  }

  if (!entry.exists()) {
    CLS_LOG(10, "log_entry_read(): entry not found");
    return -ERANGE;
  }

  if (entry.invalid()) {
    CLS_LOG(10, "log_entry_read(): entry is invalidated");
    return -ENODATA;
  }

  ret = entry.read(out);
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_read(): cannot read entry %d", ret);
    return ret;
  }

  return 0;
}

static int log_entry_write(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::WriteEntryOp>(in);
  if (!op) {
    CLS_ERR("ERROR: log_entry_write(): failed to decode input");
    return -EINVAL;
  }

  cls_zlog::LogObjectHeader header(hctx);
  int ret = header.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_write(): failed to read header %d", ret);
    return ret;
  }

  ret = header.epoch_guard(op->epoch());
  if (ret < 0) {
    CLS_LOG(10, "log_entry_write(): failed epoch guard %d", ret);
    return ret;
  }

  if (header.position_trimmed(op->position())) {
    CLS_LOG(10, "log_entry_write(): position %llu in trim range",
        op->position());
    return -EROFS;
  }

  cls_zlog::LogEntry entry(hctx, op->position());
  ret = entry.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_write(): init failed %d", ret);
    return ret;
  }

  if (entry.exists()) {
    CLS_LOG(10, "log_entry_write(): entry exists");
    return -EROFS;
  }

  std::string blob;
  if (op->data()) {
    blob = std::string(op->data()->begin(), op->data()->end());
  }

  ret = entry.set_data(blob, header.omap_max_size());
  if (ret < 0) {
    auto ms = header.omap_max_size();
    CLS_ERR("ERROR: log_entry_write(): set entry failed (b=%d) %d",
        (ms ? (int)(*ms) : -1), ret);
    return ret;
  }

  ret = entry.write();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_write(): entry write failed %d", ret);
    return ret;
  }

  if (header.update_max_pos(op->position())) {
    ret = header.write();
    if (ret < 0) {
      CLS_ERR("ERROR: log_entry_write(): header update failed %d", ret);
      return ret;
    }
  }

  return 0;
}

static int log_entry_invalidate(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::InvalidateEntryOp>(in);
  if (!op) {
    CLS_ERR("ERROR: log_entry_invalidate(): failed to decode input");
    return -EINVAL;
  }

  if (op->limit() && !op->force()) {
    CLS_ERR("ERROR: log_entry_invalidate(): limit implies force option");
    return -EINVAL;
  }

  cls_zlog::LogObjectHeader header(hctx);
  int ret = header.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_invalidate(): failed to read header %d", ret);
    return ret;
  }

  ret = header.epoch_guard(op->epoch());
  if (ret < 0) {
    CLS_LOG(10, "log_entry_invalidate(): failed epoch guard %d", ret);
    return ret;
  }

  if (op->limit()) {
    if (header.update_trim_limit(op->position())) {
      ret = header.write();
      if (ret < 0) {
        CLS_ERR("ERROR: log_entry_invalidate(): error writing header %d", ret);
        return ret;
      }
    }
    CLS_LOG(10, "log_entry_invalidate(): trim limit set %llu", op->position());
    return 0;
  }

  if (header.position_trimmed(op->position())) {
    CLS_LOG(10, "log_entry_invalidate(): position %llu in trim range",
        op->position());
    return 0;
  }

  cls_zlog::LogEntry entry(hctx, op->position());
  ret = entry.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_invalidate(): init failed %d", ret);
    return ret;
  }

  if (entry.exists()) {
    if (entry.invalid()) {
      CLS_LOG(10, "log_entry_invalidate(): already invalidated");
      return 0;
    }
    if (!op->force()) {
      CLS_LOG(10, "log_entry_invalidate(): entry exists (non-forced)");
      return -EROFS;
    }
  }

  // TODO: actually free data in omap?

  entry.invalidate();
  ret = entry.write();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_invalidate(): entry write failed %d", ret);
    return ret;
  }

  if (header.update_max_pos(op->position())) {
    ret = header.write();
    if (ret < 0) {
      CLS_ERR("ERROR: log_entry_invalidate(): header update failed %d", ret);
      return ret;
    }
  }

  return 0;
}

static int log_entry_seal(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::SealOp>(in);
  if (!op) {
    CLS_ERR("ERROR: log_entry_seal(): failed to decode input");
    return -EINVAL;
  }

  if (op->epoch() < 1) {
    CLS_ERR("ERROR: log_entry_seal(): invalid epoch %llu",
        op->epoch());
    return -EINVAL;
  }

  cls_zlog::LogObjectHeader header(hctx);
  int ret = header.read();
  if (ret < 0 && ret != -ENOENT) {
    CLS_ERR("ERROR: log_entry_seal(): failed to read header %d", ret);
    return ret;
  }

  if (ret == 0) {
    if (op->epoch() <= header.epoch()) {
      CLS_LOG(10, "log_entry_seal(): stale op epoch %llu <= %llu (hdr)",
          (unsigned long long)op->epoch(),
          (unsigned long long)header.epoch());
      return -ESPIPE;
    }
  } else if (ret != -ENOENT) {
    CLS_ERR("ERROR: unexpected return value %d", ret);
    return -EIO;
  }

  header.set_omap_max_size(op->omap_max_size());

  header.set_epoch(op->epoch());
  ret = header.write();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_seal(): write header failed %d", ret);
    return ret;
  }

  return 0;
}

static int log_entry_max_position(cls_method_context_t hctx,
    ceph::bufferlist *in, ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::ReadMaxPosOp>(in);
  if (!op) {
    CLS_ERR("ERROR: log_entry_max_position(): failed to decode input");
    return -EINVAL;
  }

  cls_zlog::LogObjectHeader header(hctx);
  int ret = header.read();
  if (ret < 0) {
    CLS_ERR("ERROR: log_entry_max_position(): failed to load header %d", ret);
    return ret;
  }

  if (op->epoch() < 1) {
    CLS_ERR("ERROR: log_entry_max_position(): invalid epoch");
    return -EINVAL;
  } else if (op->epoch() != header.epoch()) {
    CLS_LOG(10, "log_entry_max_position(): op epoch %llu != %llu (hdr)",
        (unsigned long long)op->epoch(),
        (unsigned long long)header.epoch());
    return -ESPIPE;
  }

  auto max_pos = header.max_pos();

  flatbuffers::FlatBufferBuilder fbb;
  cls_zlog::fbs::ReadMaxPosReplyBuilder builder(fbb);
  if (max_pos) {
    builder.add_position(*max_pos);
    builder.add_empty(false);
  } else {
    builder.add_empty(true);
  }
  auto reply = builder.Finish();
  fbb.Finish(reply);

  fbs_bl_encode(fbb, out);

  return 0;
}

static int head_init(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::InitHeadOp>(in);
  if (!op) {
    CLS_ERR("ERROR: head_init(): decoding input");
    return -EINVAL;
  }

  if (!op->prefix()) {
    CLS_ERR("ERROR: head_init(): prefix undefined");
    return -EINVAL;
  }

  const auto prefix = op->prefix()->str();
  if (prefix.empty()) {
    CLS_ERR("ERROR: head_init(): zero-length prefix");
    return -EINVAL;
  }

  int ret = cls_cxx_stat(hctx, NULL, NULL);
  if (ret != -ENOENT) {
    if (ret >= 0) {
      CLS_ERR("ERROR: head_init(): already init ret %d/-EEXIST", ret);
      ret = -EEXIST;
    } else {
      CLS_ERR("ERROR: head_init(): could not stat ret %d", ret);
    }
    return ret;
  }

  cls_zlog::HeadObject head(hctx, 0, prefix);
  ret = head.finalize();
  if (ret < 0) {
    CLS_ERR("ERROR: head_init(): finalizing ret %d", ret);
    return ret;
  }

  return 0;
}

static int view_create(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::CreateViewOp>(in);
  if (!op) {
    CLS_ERR("ERROR: view_create(): decoding input");
    return -EINVAL;
  }

  if (op->epoch() < 1) {
    CLS_ERR("ERROR: view_create(): invalid epoch %llu", op->epoch());
    return -EINVAL;
  }

  cls_zlog::HeadObject head(hctx);
  int ret = head.initialize();
  if (ret < 0) {
    CLS_ERR("ERROR: view_create(): initializing ret %d", ret);
    return ret;
  }

  ret = head.set_epoch(op->epoch());
  if (ret < 0) {
    CLS_ERR("ERROR: view_create(): epoch %llu hdr %llu",
        op->epoch(), head.epoch());
    return ret;
  }

  std::string blob;
  if (op->data()) {
    blob = std::string(op->data()->begin(), op->data()->end());
  }

  ret = head.write_view(blob);
  if (ret < 0) {
    CLS_ERR("ERROR: view_create(): writing view ret %d", ret);
    return ret;
  }

  ret = head.finalize();
  if (ret < 0) {
    CLS_ERR("ERROR: view_create(): finalizing ret %d", ret);
    return ret;
  }

  return 0;
}

static int view_read(cls_method_context_t hctx, ceph::bufferlist *in,
    ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::ReadViewsOp>(in);
  if (!op) {
    CLS_ERR("ERROR: view_read(): decoding input");
    return -EINVAL;
  }

  cls_zlog::HeadObject head(hctx);
  int ret = head.initialize();
  if (ret < 0) {
    CLS_ERR("ERROR: view_read(): initializing ret %d", ret);
    return ret;
  }

  uint64_t epoch = op->epoch();
  if (epoch < 1) {
    CLS_ERR("ERROR: view_read(): bad start epoch %llu", epoch);
    return -EINVAL;
  }

  uint32_t max_views = std::min(((uint32_t)op->max_views()),
      ((uint32_t)ZLOG_MAX_VIEW_READS));

  flatbuffers::FlatBufferBuilder fbb;

  uint32_t count = 0;
  std::vector<flatbuffers::Offset<cls_zlog::fbs::View>> views;
  while (epoch <= head.epoch() && count < max_views) {
    ceph::bufferlist bl;
    ret = head.read_view(epoch, &bl);
    if (ret < 0) {
      if (ret == -ENOENT) {
        // ENOENT may also be returned if the object doesn't exist, which
        // indicates to the caller that the object should be initialized. Here
        // the ENOENT case is transformed into EIO to avoid confusion, but more
        // accurately, because a missing epoch would indicate a critical error.
        CLS_ERR("ERROR: view_read(): missing epoch %llu", epoch);
        ret = -EIO;
      } else {
        CLS_ERR("ERROR: view_read(): reading view %llu ret %d", epoch, ret);
      }
      return ret;
    }

    auto data = fbb.CreateVector((uint8_t*)bl.c_str(), bl.length());
    auto view = cls_zlog::fbs::CreateView(fbb, epoch, data);
    views.push_back(view);

    epoch++;
    count++;
  }

  auto reply = cls_zlog::fbs::CreateViewsDirect(fbb, &views);
  fbb.Finish(reply);

  fbs_bl_encode(fbb, out);

  return 0;
}

static int __unique_id_read(cls_method_context_t hctx, uint64_t *pid)
{
  ceph::bufferlist bl;
  int ret = cls_cxx_getxattr(hctx, "zlog.unique_id", &bl);
  if (ret < 0) {
    return ret;
  } else {
    auto stored_id = fbs_bl_decode<cls_zlog::fbs::UniqueId>(&bl);
    if (!stored_id) {
      CLS_ERR("ERROR: __unique_id_read(): decoding stored id");
      return -EIO;
    }
    *pid = stored_id->id();
    return 0;
  }
}

static int unique_id_read(cls_method_context_t hctx,
    ceph::bufferlist *in, ceph::bufferlist *out)
{
  uint64_t id = 0;
  int ret = __unique_id_read(hctx, &id);
  if (ret < 0) {
    CLS_ERR("ERROR: unique_id_read(): read stored id ret %d", ret);
    return ret;
  }

  if (id == 0) {
    CLS_ERR("ERROR: unique_id_read(): unexpected id");
    return -EIO;
  }

  flatbuffers::FlatBufferBuilder fbb;
  auto reply = cls_zlog::fbs::CreateUniqueId(fbb, id);
  fbb.Finish(reply);

  fbs_bl_encode(fbb, out);

  return 0;
}

static int unique_id_write(cls_method_context_t hctx,
    ceph::bufferlist *in, ceph::bufferlist *out)
{
  auto op = fbs_bl_decode<cls_zlog::fbs::UniqueId>(in);
  if (!op) {
    CLS_ERR("ERROR: unique_id_write(): decoding input");
    return -EINVAL;
  }

  uint64_t id = 0; // default if not found
  int ret = __unique_id_read(hctx, &id);
  if (ret < 0) {
    if (ret == -ENOENT || ret == -ENODATA) {
      CLS_LOG(10, "unique_id_write(): no stored id found");
    } else {
      CLS_ERR("ERROR: unique_id_write(): read stored id ret %d", ret);
      return ret;
    }
  } else if (id == 0) {
    CLS_ERR("ERROR: unique_id_write(): unexpected id");
    return -EIO;
  }

  const uint64_t expected_id = id + 1;
  if (op->id() != expected_id) {
    CLS_ERR("ERROR: unique_id_write(): unexpected id %llu != %llu",
        op->id(), expected_id);
    return -ESTALE;
  }

  flatbuffers::FlatBufferBuilder fbb;
  auto unique_id = cls_zlog::fbs::CreateUniqueId(fbb, expected_id);
  fbb.Finish(unique_id);

  ceph::bufferlist bl;
  fbs_bl_encode(fbb, &bl);

  ret = cls_cxx_setxattr(hctx, "zlog.unique_id", &bl);
  if (ret < 0) {
    CLS_ERR("ERROR: unique_id_write(): setting new id ret %d", ret);
    return ret;
  }

  return 0;
}

void __cls_init()
{
  CLS_LOG(0, "loading cls_zlog");

  // log entry object methods
  cls_method_handle_t h_log_entry_read;
  cls_method_handle_t h_log_entry_write;
  cls_method_handle_t h_log_entry_invalidate;
  cls_method_handle_t h_log_entry_seal;
  cls_method_handle_t h_log_entry_max_position;

  // head object methods
  cls_method_handle_t h_head_init;
  cls_method_handle_t h_view_create;
  cls_method_handle_t h_view_read;
  cls_method_handle_t h_unique_id_read;
  cls_method_handle_t h_unique_id_write;

  cls_handle_t h_class;
  cls_register("zlog", &h_class);

  cls_register_cxx_method(h_class, "entry_read",
      CLS_METHOD_RD,
      log_entry_read, &h_log_entry_read);

  cls_register_cxx_method(h_class, "entry_write",
      CLS_METHOD_RD | CLS_METHOD_WR,
      log_entry_write, &h_log_entry_write);

  cls_register_cxx_method(h_class, "entry_invalidate",
      CLS_METHOD_RD | CLS_METHOD_WR,
      log_entry_invalidate, &h_log_entry_invalidate);

  cls_register_cxx_method(h_class, "entry_seal",
      CLS_METHOD_RD | CLS_METHOD_WR,
      log_entry_seal, &h_log_entry_seal);

  cls_register_cxx_method(h_class, "entry_max_position",
      CLS_METHOD_RD,
      log_entry_max_position, &h_log_entry_max_position);

  cls_register_cxx_method(h_class, "head_init",
      CLS_METHOD_RD | CLS_METHOD_WR,
      head_init, &h_head_init);

  cls_register_cxx_method(h_class, "view_create",
      CLS_METHOD_RD | CLS_METHOD_WR,
      view_create, &h_view_create);

  cls_register_cxx_method(h_class, "view_read",
      CLS_METHOD_RD,
      view_read, &h_view_read);

  cls_register_cxx_method(h_class, "unique_id_read",
      CLS_METHOD_RD,
      unique_id_read, &h_unique_id_read);

  cls_register_cxx_method(h_class, "unique_id_write",
      CLS_METHOD_RD | CLS_METHOD_WR,
      unique_id_write, &h_unique_id_write);
}
