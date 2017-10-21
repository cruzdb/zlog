#include <iostream>
#include <boost/exception/diagnostic_information.hpp>
#include <jni.h>

#include "com_cruzdb_Log.h"
#include "com_cruzdb_DB.h"
#include "portal.h"

static jbyteArray copyBytes(JNIEnv* env, std::string bytes) {
  const jsize jlen = static_cast<jsize>(bytes.size());

  jbyteArray jbytes = env->NewByteArray(jlen);
  if(jbytes == nullptr) {
    // exception thrown: OutOfMemoryError
    return nullptr;
  }

  env->SetByteArrayRegion(jbytes, 0, jlen,
      const_cast<jbyte*>(reinterpret_cast<const jbyte*>(bytes.c_str())));
  if(env->ExceptionCheck()) {
    // exception thrown: ArrayIndexOutOfBoundsException
    env->DeleteLocalRef(jbytes);
    return nullptr;
  }

  return jbytes;
}

void Java_com_cruzdb_Log_disposeInternal(
    JNIEnv *env, jobject jobj, jlong jhandle)
{
  delete reinterpret_cast<LogWrapper*>(jhandle);
}

void Java_com_cruzdb_DB_disposeInternal(JNIEnv *env, jobject jobj,
    jlong jhandle)
{
  delete reinterpret_cast<DB*>(jhandle);
}

void Java_com_cruzdb_DB_openNative(JNIEnv *env, jobject jobj,
    jlong jdbHandle, jboolean jcreate)
{
  auto log = reinterpret_cast<LogWrapper*>(jdbHandle);

  DB *db;
  int ret = DB::Open(log->log, jcreate, &db);
  if (ret) {
    ZlogExceptionJni::ThrowNew(env, ret);
    return;
  }

  ZlogDBJni::setHandle(env, jobj, db);
}

void Java_com_cruzdb_DB_put(JNIEnv *env, jobject jdb, jlong jdbHandle,
    jbyteArray jkey, jint jkeyOffset, jint jkeyLength, jbyteArray jval,
    jint jvalOffset, jint jvalLength)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if (env->ExceptionCheck()) {
    delete [] key;
    return;
  }

  jbyte *value = new jbyte[jvalLength];
  env->GetByteArrayRegion(jval, jvalOffset, jvalLength, value);
  if (env->ExceptionCheck()) {
    delete [] value;
    delete [] key;
    return;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);
  Slice value_slice(reinterpret_cast<char*>(value), jvalLength);

  auto txn = db->BeginTransaction();
  txn->Put(key_slice, value_slice);
  txn->Commit();
  delete txn;

  delete [] value;
  delete [] key;
}

jint Java_com_cruzdb_DB_get(JNIEnv *env, jobject jdb, jlong jdbHandle,
    jbyteArray jkey, jint jkeyOffset, jint jkeyLength, jbyteArray jval,
    jint jvalOffset, jint jvalLength)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if (env->ExceptionCheck()) {
    delete [] key;
    return -2;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  std::string value;
  int ret = db->Get(key_slice, &value);

  delete [] key;

  if (ret == -ENOENT)
    return -1;

  const jint value_length = static_cast<jint>(value.size());
  const jint length = std::min(jvalLength, value_length);
  env->SetByteArrayRegion(jval, jvalOffset, length,
      const_cast<jbyte*>(reinterpret_cast<const jbyte*>(value.c_str())));
  if (env->ExceptionCheck()) {
    return -2;
  }

  return value_length;
}

jbyteArray Java_com_cruzdb_DB_get__J_3BII
  (JNIEnv *env, jobject jdb, jlong jdbHandle, jbyteArray jkey,
   jint jkeyOffset, jint jkeyLength)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if (env->ExceptionCheck()) {
    delete [] key;
    return nullptr;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  std::string value;
  int ret = db->Get(key_slice, &value);

  delete [] key;

  if (ret == -ENOENT)
    return nullptr;

  jbyteArray jret_value = copyBytes(env, value);
  if (jret_value == nullptr)
    return nullptr;
  return jret_value;
}

void Java_com_cruzdb_DB_delete(JNIEnv *env, jobject jdb, jlong jdbHandle,
    jbyteArray jkey, jint jkeyOffset, jint jkeyLength)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if(env->ExceptionCheck()) {
    delete [] key;
    return;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  auto *txn = db->BeginTransaction();
  txn->Delete(key_slice);
  txn->Commit();
  delete txn;

  delete [] key;
}

jlong Java_com_cruzdb_DB_iterator(JNIEnv *env, jobject jdb,
    jlong jdbHandle)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);
  auto *iterator = db->NewIterator();
  return reinterpret_cast<jlong>(iterator);
}

jlong Java_com_cruzdb_DB_transaction(JNIEnv *env, jobject jdb,
    jlong jdbHandle)
{
  auto *db = reinterpret_cast<DB*>(jdbHandle);
  auto *txn = db->BeginTransaction();
  return reinterpret_cast<jlong>(txn);
}

void Java_com_cruzdb_Log_openLMDBNative(JNIEnv *env, jobject jobj,
    jstring jdb_path, jstring jlog_name)
{
  auto log = std::unique_ptr<LogWrapper>(new LogWrapper);
  std::map<std::string, std::string> opts;

  const char *db_path = env->GetStringUTFChars(jdb_path, 0);
  opts["path"] = db_path;
  env->ReleaseStringUTFChars(jdb_path, db_path);

  const char *log_name = env->GetStringUTFChars(jlog_name, 0);
  int ret = zlog::Log::Open("lmdb", log_name, opts,
      "", "", &log->log);
  if (ret == -ENOENT) {
    ret = zlog::Log::Create("lmdb", log_name, opts,
        "", "", &log->log);
  }
  env->ReleaseStringUTFChars(jlog_name, log_name);
  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log.release());
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);
}

void Java_com_cruzdb_Log_openNative(JNIEnv *env, jobject jobj, jstring jpool,
    jstring jseqr_server, jint jseqr_port, jstring jlog_name)
{
  auto log = std::unique_ptr<LogWrapper>(new LogWrapper);
  std::map<std::string, std::string> opts;

  const char *pool = env->GetStringUTFChars(jpool, 0);
  opts["pool"] = pool;
  env->ReleaseStringUTFChars(jpool, pool);

  const char *c_server = env->GetStringUTFChars(jseqr_server, 0);
  std::string server = c_server;
  env->ReleaseStringUTFChars(jseqr_server, c_server);

  std::stringstream port;
  port << jseqr_port;

  const char *log_name = env->GetStringUTFChars(jlog_name, 0);
  int ret = zlog::Log::Create("ceph", log_name, opts,
      server, port.str(), &log->log);
  env->ReleaseStringUTFChars(jlog_name, log_name);
  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log.release());
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);
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
