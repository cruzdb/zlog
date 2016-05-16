package com.cruzdb;

import java.io.IOException;

/**
 * A Log is a high-performance linearizable shared-log.
 *
 * @see <a target="_blank" href="http://github.com/noahdesu/zlog">http://github.com/noahdesu/zlog</a>
 * @see <a target="_blank" href="http://noahdesu.github.io/2014/10/26/corfu-on-ceph.html">http://noahdesu.github.io/2014/10/26/corfu-on-ceph.html</a>
 */
public class Log extends ZObject {

  static {
    Log.loadLibrary();
  }

  /**
   *
   */
  public static synchronized void loadLibrary() {
    String tmpDir = System.getenv("ZLOG_SHAREDLIB_DIR");
    try {
      NativeLibraryLoader.getInstance().loadLibrary(tmpDir);
    } catch (IOException e) {
      throw new RuntimeException("Unable to load the ZLog shared library: " + e);
    }
  }

  @Override
  protected void disposeInternal() {
    synchronized (this) {
      assert(isInitialized());
      disposeInternal(nativeHandle_);
    }
  }

  private Log() {
    super();
  }

  /**
   *
   */
  public static Log open(final String pool, final String seqr_server,
      int seqr_port, String log_name) throws LogException {
    Log log = new Log();
    log.openNative(pool, seqr_server, seqr_port, log_name);
    return log;
  }

  /**
   * Append "data" to the tail of the log.
   *
   * @param data the data to be appended.
   * @return the log position where data was written.
   *
   * @throws LogException thrown if an error occurs in the underlying native
   * library.
   */
  public long append(final byte[] data) throws LogException {
    return append(nativeHandle_, data, data.length);
  }

  /**
   * Read data from a "position" in the log.
   *
   * @param position the log position to read.
   * @return a byte array storing the value associated with the log position,
   * if any. null if an error occurs.
   *
   * @throws NotWrittenException thrown if the log position has not been
   * written.
   * @throws FilledException thrown if the log position has been filled.
   * @throws LogException thrown if an error occurs in the underlying native
   * library.
   */
  public byte[] read(long position) throws LogException {
    return read(nativeHandle_, position);
  }

  /**
   * Fill a "position" in the log.
   *
   * @param position the log position to fill.
   * 
   * @throws ReadOnlyException thrown if the log position has been written.
   * @throws LogException thrown if an error occurs in the underlying native
   * library.
   */
  public void fill(long position) throws LogException {
    fill(nativeHandle_, position);
  }

  /**
   * Trim a "position" in the log.
   *
   * @param position the log position to trim.
   * 
   * @throws LogException thrown if an error occurs in the underlying native
   * library.
   */
  public void trim(long position) throws LogException {
    trim(nativeHandle_, position);
  }

  /**
   * Find the tail of the log.
   *
   * @return the log tail position.
   *
   * @throws LogException thrown if an error occurs in the underlying native
   * library.
   */
  public long tail() throws LogException {
    return tail(nativeHandle_);
  }

  private native void disposeInternal(long handle);
  private native void openNative(String pool, String seqr_server,
      int seqr_port, String log_name) throws LogException;
  private native long append(long handle, byte[] data, int dataLen) throws LogException;
  private native byte[] read(long handle, long position) throws LogException;
  private native void fill(long handle, long position) throws LogException;
  private native void trim(long handle, long position) throws LogException;
  private native long tail(long handle) throws LogException;
  private native long kv_insert(long handle)...
}
