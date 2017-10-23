#include <iostream>
#include <boost/exception/diagnostic_information.hpp>
#include <jni.h>

#include "com_cruzdb_Log.h"
#include "portal.h"

void Java_com_cruzdb_Log_disposeInternal(
    JNIEnv *env, jobject jobj, jlong jhandle)
{
  delete reinterpret_cast<zlog::Log*>(jhandle);
}

void Java_com_cruzdb_Log_openLMDBNative(JNIEnv *env, jobject jobj,
    jstring jdb_path, jstring jlog_name)
{
  std::map<std::string, std::string> opts;

  const char *db_path = env->GetStringUTFChars(jdb_path, 0);
  opts["path"] = db_path;
  env->ReleaseStringUTFChars(jdb_path, db_path);

  zlog::Log *log;
  const char *log_name = env->GetStringUTFChars(jlog_name, 0);
  int ret = zlog::Log::Open("lmdb", log_name, opts,
      "", "", &log);
  if (ret == -ENOENT) {
    ret = zlog::Log::Create("lmdb", log_name, opts,
        "", "", &log);
  }
  env->ReleaseStringUTFChars(jlog_name, log_name);
  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log);
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);
}

void Java_com_cruzdb_Log_openNative(JNIEnv *env, jobject jobj, jstring jpool,
    jstring jseqr_server, jint jseqr_port, jstring jlog_name)
{
  std::map<std::string, std::string> opts;

  const char *pool = env->GetStringUTFChars(jpool, 0);
  opts["pool"] = pool;
  env->ReleaseStringUTFChars(jpool, pool);

  const char *c_server = env->GetStringUTFChars(jseqr_server, 0);
  std::string server = c_server;
  env->ReleaseStringUTFChars(jseqr_server, c_server);

  std::stringstream port;
  port << jseqr_port;

  zlog::Log *log;
  const char *log_name = env->GetStringUTFChars(jlog_name, 0);
  int ret = zlog::Log::Create("ceph", log_name, opts,
      server, port.str(), &log);
  env->ReleaseStringUTFChars(jlog_name, log_name);
  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log);
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);
}

jlong Java_com_cruzdb_Log_append(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jbyteArray jdata, jint jdata_len)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  jbyte *data = env->GetByteArrayElements(jdata, 0);

  uint64_t position;
  int ret = log->Append(Slice((char*)data, jdata_len), &position);
  ZlogExceptionJni::ThrowNew(env, ret);
  env->ReleaseByteArrayElements(jdata, data, JNI_ABORT);

  return position;
}

jbyteArray Java_com_cruzdb_Log_read(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position = jpos;
  std::string entry;

  int ret = log->Read(position, &entry);
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
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position = jpos;
  int ret = log->Fill(position);
  if (ret == -EROFS)
    ReadOnlyExceptionJni::ThrowNew(env, ret);
  else
    ZlogExceptionJni::ThrowNew(env, ret);
}

void Java_com_cruzdb_Log_trim(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position = jpos;
  int ret = log->Trim(position);
  ZlogExceptionJni::ThrowNew(env, ret);
}

jlong Java_com_cruzdb_Log_tail(JNIEnv *env, jobject jlog,
    jlong jlog_handle)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position;
  int ret = log->CheckTail(&position);
  ZlogExceptionJni::ThrowNew(env, ret);
  return position;
}
