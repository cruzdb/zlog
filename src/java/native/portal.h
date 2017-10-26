#ifndef ZLOG_JNI_PORTAL_H
#define ZLOG_JNI_PORTAL_H

#include <jni.h>
#include <cassert>
#include <sstream>
#include "zlog/log.h"
#include "zlog/slice.h"

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

class ZlogJni : public ZlogNativeClass<zlog::Log*, ZlogJni> {
 public:
  static jclass getJClass(JNIEnv *env) {
    return ZlogNativeClass::getJClass(env, "org/cruzdb/zlog/Log");
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
    return ZlogJavaException::getJClass(env, "org/cruzdb/zlog/LogException");
  }
};

class ReadOnlyExceptionJni : public ZlogJavaException<ReadOnlyExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "org/cruzdb/zlog/ReadOnlyException");
  }
};

class FilledExceptionJni : public ZlogJavaException<FilledExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "org/cruzdb/zlog/FilledException");
  }
};

class NotWrittenExceptionJni : public ZlogJavaException<NotWrittenExceptionJni> {
 public:
  static jclass getJClass(JNIEnv* env) {
    return ZlogJavaException::getJClass(env, "org/cruzdb/zlog/NotWrittenException");
  }
};

#endif
