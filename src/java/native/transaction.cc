#include <stdio.h>
#include <stdlib.h>
#include <jni.h>

#include "com_cruzdb_Transaction.h"
#include "zlog/transaction.h"
#include "portal.h"

// TODO: put in common location
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

void Java_com_cruzdb_Transaction_disposeInternal
  (JNIEnv *env, jobject jtxn, jlong jtxnHandle)
{
  delete reinterpret_cast<Transaction*>(jtxnHandle);
}

void Java_com_cruzdb_Transaction_put(JNIEnv *env, jobject jtxn, jlong jtxnHandle,
    jbyteArray jkey, jint jkeyOffset, jint jkeyLength, jbyteArray jval,
    jint jvalOffset, jint jvalLength)
{
  auto *txn = reinterpret_cast<Transaction*>(jtxnHandle);

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

  txn->Put(key_slice, value_slice);

  delete [] value;
  delete [] key;
}

jbyteArray Java_com_cruzdb_Transaction_get(JNIEnv *env, jobject jtxn,
    jlong jtxnHandle, jbyteArray jkey, jint jkeyOffset, jint jkeyLength)
{
  auto *txn = reinterpret_cast<Transaction*>(jtxnHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if (env->ExceptionCheck()) {
    delete [] key;
    return nullptr;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  std::string value;
  int ret = txn->Get(key_slice, &value);

  delete [] key;

  if (ret == -ENOENT)
    return nullptr;

  if (ret) {
    ZlogExceptionJni::ThrowNew(env, ret);
    return nullptr;
  }

  jbyteArray jret_value = copyBytes(env, value);
  if (jret_value == nullptr)
    return nullptr;
  return jret_value;
}

void Java_com_cruzdb_DB_delete(JNIEnv *env, jobject jtxn, jlong jtxnHandle,
    jbyteArray jkey, jint jkeyOffset, jint jkeyLength)
{
  auto *txn = reinterpret_cast<Transaction*>(jtxnHandle);

  jbyte *key = new jbyte[jkeyLength];
  env->GetByteArrayRegion(jkey, jkeyOffset, jkeyLength, key);
  if(env->ExceptionCheck()) {
    delete [] key;
    return;
  }

  Slice key_slice(reinterpret_cast<char*>(key), jkeyLength);

  txn->Delete(key_slice);

  delete [] key;
}

void Java_com_cruzdb_Transaction_commit(JNIEnv *env, jobject jtxn,
    jlong jtxnHandle)
{
  auto *txn = reinterpret_cast<Transaction*>(jtxnHandle);
  txn->Commit();
}

void Java_com_cruzdb_Transaction_abort(JNIEnv *env, jobject jtxn,
    jlong jtxnHandle)
{
  auto *txn = reinterpret_cast<Transaction*>(jtxnHandle);
  txn->Abort();
}
