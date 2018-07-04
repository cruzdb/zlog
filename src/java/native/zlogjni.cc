#include <iostream>
#include <boost/exception/diagnostic_information.hpp>
#include <jni.h>

#include "org_cruzdb_zlog_Log.h"
#include "portal.h"

void Java_org_cruzdb_zlog_Log_disposeInternal(
    JNIEnv *env, jobject jobj, jlong jhandle)
{
  delete reinterpret_cast<zlog::Log*>(jhandle);
}

zlog::Options options;

JNIEXPORT void JNICALL Java_org_cruzdb_zlog_Log_openNative
  (JNIEnv *env, jobject jobj, jstring jscheme,
   jobjectArray jkeys, jobjectArray jvals, jstring jname)
{
  const jsize len_opts = env->GetArrayLength(jkeys);
  assert(len_opts == env->GetArrayLength(jvals));

  std::map<std::string, std::string> opts;
  for (jsize i = 0; i < len_opts; i++) {
    jobject jobj_key = env->GetObjectArrayElement(jkeys, i);
    if (env->ExceptionCheck()) {
      return;
    }

    jobject jobj_val = env->GetObjectArrayElement(jvals, i);
    if (env->ExceptionCheck()) {
      env->DeleteLocalRef(jobj_key);
      return;
    }

    jstring jkey = reinterpret_cast<jstring>(jobj_key);
    jstring jval = reinterpret_cast<jstring>(jobj_val);

    const char *key = env->GetStringUTFChars(jkey, 0);
    if (key == nullptr) {
      env->DeleteLocalRef(jobj_val);
      env->DeleteLocalRef(jobj_key);
      return;
    }

    const char *val = env->GetStringUTFChars(jval, 0);
    if (val == nullptr) {
      env->ReleaseStringUTFChars(jkey, key);
      env->DeleteLocalRef(jobj_val);
      env->DeleteLocalRef(jobj_key);
      return;
    }

    opts[key] = val;

    env->ReleaseStringUTFChars(jval, val);
    env->ReleaseStringUTFChars(jkey, key);
    env->DeleteLocalRef(jobj_val);
    env->DeleteLocalRef(jobj_key);
  }

  const char *scheme = env->GetStringUTFChars(jscheme, 0);
  if (scheme == nullptr) {
    return;
  }

  const char *name = env->GetStringUTFChars(jname, 0);
  if (name == nullptr) {
    env->ReleaseStringUTFChars(jscheme, scheme);
    return;
  }

  zlog::Log *log;
  int ret = zlog::Log::Create(options, scheme, name, opts, "", "", &log);

  env->ReleaseStringUTFChars(jscheme, scheme);
  env->ReleaseStringUTFChars(jname, name);

  if (ret)
    goto out;

  ZlogJni::setHandle(env, jobj, log);
  return;

out:
  ZlogExceptionJni::ThrowNew(env, ret);
}

jlong Java_org_cruzdb_zlog_Log_append(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jbyteArray jdata, jint jdata_len)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  jbyte *data = env->GetByteArrayElements(jdata, 0);

  uint64_t position;
  int ret = log->Append(zlog::Slice((char*)data, jdata_len), &position);
  ZlogExceptionJni::ThrowNew(env, ret);
  env->ReleaseByteArrayElements(jdata, data, JNI_ABORT);

  return position;
}

jbyteArray Java_org_cruzdb_zlog_Log_read(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position = jpos;
  std::string entry;

  int ret = log->Read(position, &entry);
  if (ret) {
    if (ret == -ENOENT)
      NotWrittenExceptionJni::ThrowNew(env, ret);
    else if (ret == -ENODATA)
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

void Java_org_cruzdb_zlog_Log_fill(JNIEnv *env, jobject jlog,
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

void Java_org_cruzdb_zlog_Log_trim(JNIEnv *env, jobject jlog,
    jlong jlog_handle, jlong jpos)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position = jpos;
  int ret = log->Trim(position);
  ZlogExceptionJni::ThrowNew(env, ret);
}

jlong Java_org_cruzdb_zlog_Log_tail(JNIEnv *env, jobject jlog,
    jlong jlog_handle)
{
  auto log = reinterpret_cast<zlog::Log*>(jlog_handle);

  uint64_t position;
  int ret = log->CheckTail(&position);
  ZlogExceptionJni::ThrowNew(env, ret);
  return position;
}
