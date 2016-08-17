#include <iostream>
#include <boost/exception/diagnostic_information.hpp>
#include <jni.h>

#include "com_cruzdb_Log.h"
#include "portal.h"
#include "zlog/ceph_backend.h"

void Java_com_cruzdb_Log_disposeInternal(
    JNIEnv *env, jobject jobj, jlong jhandle)
{
  std::cout << "delete" << std::endl;
  delete reinterpret_cast<LogWrapper*>(jhandle);
}

void Java_com_cruzdb_Log_openNative(JNIEnv *env, jobject jobj, jstring jpool,
    jstring jseqr_server, jint jseqr_port, jstring jlog_name)
{
  std::stringstream port;
  const char *seqr_server;
  const char *log_name;
  const char *pool;
  LogWrapper *log = new LogWrapper;
  // FIXME: this is a memory leak!
  CephBackend *be;

  /*
   * Connect to RADOS
   */
  int ret = log->rados.init(NULL);
  if (ret)
    goto out;

  ret = log->rados.conf_read_file(NULL);
  if (ret)
    goto out;

  ret = log->rados.conf_parse_env(NULL);
  if (ret)
    goto out;

  ret = log->rados.connect();
  if (ret)
    goto out;

  pool = env->GetStringUTFChars(jpool, 0);
  ret = log->rados.ioctx_create(pool, log->ioctx);
  env->ReleaseStringUTFChars(jpool, pool);
  if (ret)
    goto out;

  /*
   * Connect to sequencer
   */
  port << jseqr_port;
  seqr_server = env->GetStringUTFChars(jseqr_server, 0);
  log->seqr_client = new zlog::SeqrClient(seqr_server, port.str().c_str());
  env->ReleaseStringUTFChars(jseqr_server, seqr_server);
  try {
    log->seqr_client->Connect();
  } catch (...) {
    ZlogExceptionJni::ThrowNew(env,
        boost::current_exception_diagnostic_information());
    goto out_noexcept;
  }

  // FIXME: this is a memory leak!
  be = new CephBackend(&log->ioctx);

  log_name = env->GetStringUTFChars(jlog_name, 0);
  ret = zlog::Log::OpenOrCreate(be, log_name, log->seqr_client, &log->log);
  env->ReleaseStringUTFChars(jlog_name, log_name);
  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log);
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);

out_noexcept:
  delete log;
}

jlong Java_com_cruzdb_Log_append(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jbyteArray jdata, jint jdata_len)
{
  auto log = reinterpret_cast<LogWrapper*>(jlog_handle);

  jbyte *data = env->GetByteArrayElements(jdata, 0);

  uint64_t position;
  int ret = log->log->Append(Slice((char*)data, jdata_len), &position);
  ZlogExceptionJni::ThrowNew(env, ret);
  env->ReleaseByteArrayElements(jdata, data, JNI_ABORT);

  return position;
}

jbyteArray Java_com_cruzdb_Log_read(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<LogWrapper*>(jlog_handle);

  uint64_t position = jpos;
  std::string entry;

  int ret = log->log->Read(position, &entry);
  if (ret) {
    if (ret == -ENODEV)
      NotWrittenExceptionJni::ThrowNew(env, ret);
    else if (ret == -EFAULT)
      FilledExceptionJni::ThrowNew(env, ret);
    else
      ZlogExceptionJni::ThrowNew(env, ret);
    return nullptr;
  }

  jbyteArray result = env->NewByteArray(static_cast<jsize>(entry.size()));
  env->SetByteArrayRegion(result, 0, static_cast<jsize>(entry.size()),
      reinterpret_cast<const jbyte*>(entry.data()));
  return result;
}

void Java_com_cruzdb_Log_fill(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<LogWrapper*>(jlog_handle);

  uint64_t position = jpos;
  int ret = log->log->Fill(position);
  if (ret == -EROFS)
    ReadOnlyExceptionJni::ThrowNew(env, ret);
  else
    ZlogExceptionJni::ThrowNew(env, ret);
}

void Java_com_cruzdb_Log_trim(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<LogWrapper*>(jlog_handle);

  uint64_t position = jpos;
  int ret = log->log->Trim(position);
  ZlogExceptionJni::ThrowNew(env, ret);
}

jlong Java_com_cruzdb_Log_tail(JNIEnv *env, jobject jlog,
    jlong jlog_handle)
{
  auto log = reinterpret_cast<LogWrapper*>(jlog_handle);

  uint64_t position;
  int ret = log->log->CheckTail(&position);
  ZlogExceptionJni::ThrowNew(env, ret);
  return position;
}
