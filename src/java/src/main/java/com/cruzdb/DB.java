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
   * @param log the log used to store the database.
   * @param create create the log if it doesn't exist.
   * @return database instance.
   * @throws com.cruzdb.LogException if an error occurs in the native library.
   */
  public static DB open(Log log, boolean create) throws LogException {
    DB db = new DB();
    db.openNative(log.nativeHandle_, create);
    return db;
  }

  /**
   * @param key the key to be inserted.
   * @param value the value associated with the key.
   * @throws com.cruzdb.LogException if an error occurs in the native library.
   */
  public void put(final byte[] key, final byte[] value) throws LogException {
    put(nativeHandle_, key, 0, key.length, value, 0, value.length);
  }

  /**
   * @param key the key to be inserted.
   * @param value the value associated with the key.
   * @return size of value.
   * @throws com.cruzdb.LogException if an error occurs in the native library.
   */
  public int get(final byte[] key, final byte[] value) throws LogException {
    return get(nativeHandle_, key, 0, key.length, value, 0, value.length);
  }

  /**
   * @param key the key to be inserted.
   * @return the value of the associated key.
   * @throws com.cruzdb.LogException if an error occurs in the native library.
   */
  public byte[] get(final byte[] key) throws LogException {
    return get(nativeHandle_, key, 0, key.length);
  }

  /**
   * @param key the key of the entry to be deleted.
   * @throws com.cruzdb.LogException if an error occurs in the native library.
   */
  public void delete(final byte[] key) throws LogException {
    delete(nativeHandle_, key, 0, key.length);
  }

  /**
   * @return a new iterator.
   */
  public CruzIterator newIterator() {
    return new CruzIterator(this, iterator(nativeHandle_));
  }

  /**
   * @return a new transaction.
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
