#include <stdio.h>
#include <stdlib.h>
#include <jni.h>

#include "com_cruzdb_CruzIterator.h"
#include "zlog/iterator.h"
#include "portal.h"

void Java_com_cruzdb_CruzIterator_disposeInternal(JNIEnv *env,
    jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  assert(it != nullptr);
  delete it;
}

jboolean Java_com_cruzdb_CruzIterator_isValid0
  (JNIEnv *env, jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  return it->Valid();
}

void Java_com_cruzdb_CruzIterator_seekToFirst0
  (JNIEnv *env, jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  it->SeekToFirst();
}

void Java_com_cruzdb_CruzIterator_seekToLast0
  (JNIEnv *env, jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  it->SeekToLast();
}

void Java_com_cruzdb_CruzIterator_next0
  (JNIEnv *env, jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  it->Next();
}

void Java_com_cruzdb_CruzIterator_prev0
  (JNIEnv *env, jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  it->Prev();
}

void Java_com_cruzdb_CruzIterator_seek0
  (JNIEnv *env, jobject jit, jlong jitHandle,
   jbyteArray jkey, jint jkeyLength)
{
  jbyte *key = env->GetByteArrayElements(jkey, nullptr);
  if (key == nullptr)
    return;

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  it->Seek(key_slice);

  env->ReleaseByteArrayElements(jkey, key, JNI_ABORT);
}

jbyteArray Java_com_cruzdb_CruzIterator_key0(JNIEnv *env,
    jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  Slice key_slice = it->key();
  jbyteArray jkey = env->NewByteArray(static_cast<jsize>(key_slice.size()));
  if (jkey == nullptr)
    return nullptr;
  env->SetByteArrayRegion(jkey, 0, static_cast<jsize>(key_slice.size()),
      const_cast<jbyte*>(reinterpret_cast<const jbyte*>(key_slice.data())));
  return jkey;
}

jbyteArray Java_com_cruzdb_CruzIterator_value0(JNIEnv *env,
    jobject jit, jlong jitHandle)
{
  auto *it = reinterpret_cast<Iterator*>(jitHandle);
  Slice value_slice = it->value();
  jbyteArray jvalue = env->NewByteArray(static_cast<jsize>(value_slice.size()));
  if (jvalue == nullptr)
    return nullptr;
  env->SetByteArrayRegion(jvalue, 0, static_cast<jsize>(value_slice.size()),
      const_cast<jbyte*>(reinterpret_cast<const jbyte*>(value_slice.data())));
  return jvalue;
}
