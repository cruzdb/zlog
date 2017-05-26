package com.cruzdb;

public class DB extends ZObject {

  public static final int NOT_FOUND = -1;

  @Override
  protected void disposeInternal() {
    synchronized (this) {
      assert(isInitialized());
      disposeInternal(nativeHandle_);
    }
  }

  private DB() {
    super();
  }

  /**
   *
   */
  public static DB open(Log log, boolean create) throws LogException {
    DB db = new DB();
    db.openNative(log.nativeHandle_, create);
    return db;
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
  public int get(final byte[] key, final byte[] value) throws LogException {
    return get(nativeHandle_, key, 0, key.length, value, 0, value.length);
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
  public CruzIterator newIterator() {
    return new CruzIterator(this, iterator(nativeHandle_));
  }

  /**
   *
   */
  public Transaction newTransaction() {
    return new Transaction(this, transaction(nativeHandle_));
  }

  private native void disposeInternal(long handle);
  private native void openNative(long dbHandle, boolean create) throws LogException;
  private native void put(long handle, byte[] key, int keyOffset, int keyLength,
      byte[] value, int valueOffset, int valueLength) throws LogException;
  private native int get(long handle, byte[] key, int keyOffset, int keyLength,
      byte[] value, int valueOffset, int valueLength) throws LogException;
  private native byte[] get(long handle, byte[] key, int keyOffset,
      int keyLength) throws LogException;
  private native void delete(long handle, byte[] key, int keyOffset,
      int keyLength) throws LogException;
  private native long iterator(long handle);
  private native long transaction(long handle);
}
