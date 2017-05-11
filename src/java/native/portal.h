#ifndef ZLOG_JNI_PORTAL_H
#define ZLOG_JNI_PORTAL_H

#include <jni.h>
#include <cassert>
#include "zlog/log.h"
#include "zlog/backend.h"

#include "zlog/backend/lmdb.h"
#include "zlog/backend/fakeseqr.h"

#ifdef WITH_RADOS
# include <rados/librados.hpp>
# include "zlog/backend/ceph.h"
#endif

template<class PTR, class DERIVED> class ZlogNativeClass {
 public:
  static jclass getJClass(JNIEnv *env, const char *jclazz_name) {
    jclass jclazz = env->FindClass(jclazz_name);
    assert(jclazz != nullptr);
    return jclazz;
  }

  static jfieldID getHandleFieldID(JNIEnv *env) {
    static jfieldID fid = env->GetFieldID(
        DERIVED::getJClass(env), "nativeHandle_", "J");
    assert(fid != nullptr);
    return fid;
  }

  static PTR getHandle(JNIEnv *env, jobject jobj) {
    return reinterpret_cast<PTR>(
        env->GetLongField(jobj, getHandleFieldID(env)));
  }

  static void setHandle(JNIEnv *env, jobject jobj, PTR ptr) {
    env->SetLongField(jobj, getHandleFieldID(env),
        reinterpret_cast<jlong>(ptr));
  }
};

class LogWrapper {
 public:
  LogWrapper() :
    be(nullptr),
    log(nullptr),
    seqr_client(nullptr)
  {}

  ~LogWrapper() {
    if (log)
      delete log;
    if (seqr_client)
      delete seqr_client;
    if (be)
      delete be;
  }

  Backend *be;
  zlog::Log *log;
  zlog::SeqrClient *seqr_client;

#ifdef WITH_RADOS
  librados::Rados rados;
  librados::IoCtx ioctx;
#endif
};

class ZlogJni : public ZlogNativeClass<LogWrapper*, ZlogJni> {
 public:
  static jclass getJClass(JNIEnv *env) {
    return ZlogNativeClass::getJClass(env, "com/cruzdb/Log");
  }
};

template<class DERIVED>
class ZlogJavaException {
 public:
  static jclass getJClass(JNIEnv *env, const char *jclazz_name) {
    jclass jclazz = env->FindClass(jclazz_name);
    assert(jclazz != nullptr);
    return jclazz;
  }

  static void ThrowNew(JNIEnv *env, std::string cmsg) {
    jstring msg = env->NewStringUTF(cmsg.c_str());
    ThrowNew(env, msg);
  }

  static void ThrowNew(JNIEnv *env, int errcode) {
    if (!errcode)
      return;
    std::stringstream err;
    err << "error: errno=" << errcode;
    jstring msg = env->NewStringUTF(err.str().c_str());
    ThrowNew(env, msg);
  }

  static void ThrowNew(JNIEnv *env, jstring msg) {
    static jmethodID mid = env->GetMethodID(DERIVED::getJClass(env),
        "<init>", "(Ljava/lang/String;)V");
    assert(mid != nullptr);
    env->Throw((jthrowable)env->NewObject(DERIVED::getJClass(env),
          mid, msg));
  }
};

class ZlogExceptionJni : public ZlogJavaException<ZlogExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "com/cruzdb/LogException");
  }
};

class ReadOnlyExceptionJni : public ZlogJavaException<ReadOnlyExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "com/cruzdb/ReadOnlyException");
  }
};

class FilledExceptionJni : public ZlogJavaException<FilledExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "com/cruzdb/FilledException");
  }
};

class NotWrittenExceptionJni : public ZlogJavaException<NotWrittenExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "com/cruzdb/NotWrittenException");
  }
};

#endif
