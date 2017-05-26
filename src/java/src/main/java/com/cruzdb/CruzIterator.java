package com.cruzdb;

public class CruzIterator extends ZObject {
  final DB db;

  @Override
  protected void disposeInternal() {
    synchronized (this) {
      assert(isInitialized());
      disposeInternal(nativeHandle_);
    }
  }

  CruzIterator(DB db, long nativeHandle) {
    super(nativeHandle);
    this.db = db;
  }

  /**
   *
   */
  public byte[] key() {
    return key0(nativeHandle_);
  }

  /**
   *
   */
  public byte[] value() {
    return value0(nativeHandle_);
  }

  /**
   *
   */
  public boolean isValid() {
    return isValid0(nativeHandle_);
  }

  /**
   *
   */
  public void seekToFirst() {
    seekToFirst0(nativeHandle_);
  }

  /**
   *
   */
  public void seekToLast() {
    seekToLast0(nativeHandle_);
  }

  /**
   *
   */
  public void seek(byte[] target) {
    seek0(nativeHandle_, target, target.length);
  }

  /**
   *
   */
  public void next() {
    next0(nativeHandle_);
  }

  /**
   *
   */
  public void prev() {
    prev0(nativeHandle_);
  }

  private native void disposeInternal(long handle);
  private native boolean isValid0(long handle);
  private native void seekToFirst0(long handle);
  private native void seekToLast0(long handle);
  private native void next0(long handle);
  private native void prev0(long handle);
  private native void seek0(long handle, byte[] target, int targetLen);
  private native byte[] key0(long handle);
  private native byte[] value0(long handle);
}
