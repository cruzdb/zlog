package com.cruzdb;

public class Transaction extends ZObject {
  final DB db;

  @Override
  protected void disposeInternal() {
    synchronized (this) {
      assert(isInitialized());
      disposeInternal(nativeHandle_);
    }
  }

  Transaction(DB db, long nativeHandle) {
    super(nativeHandle);
    this.db = db;
  }

  /**
   *
   */
  public void put(final byte[] key, final byte[] value) throws LogException {
    put(nativeHandle_, key, 0, key.length, value, 0, value.length);
  }

  /**
   *
   */
  public byte[] get(final byte[] key) throws LogException {
    return get(nativeHandle_, key, 0, key.length);
  }

  /**
   *
   */
  public void delete(final byte[] key) throws LogException {
    delete(nativeHandle_, key, 0, key.length);
  }

  /**
   *
   */
  public void commit() throws LogException {
    commit(nativeHandle_);
  }

  /**
   *
   */
  public void abort() throws LogException {
    abort(nativeHandle_);
  }

  private native void disposeInternal(long handle);
  private native void put(long handle, byte[] key, int keyOffset, int keyLength,
      byte[] value, int valueOffset, int valueLength) throws LogException;
  private native byte[] get(long handle, byte[] key, int keyOffset,
      int keyLength) throws LogException;
  private native void delete(long handle, byte[] key, int keyOffset,
      int keyLength) throws LogException;
  private native void commit(long handle) throws LogException;
  private native void abort(long handle) throws LogException;
}
