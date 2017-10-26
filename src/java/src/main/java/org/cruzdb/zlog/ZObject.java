package org.cruzdb.zlog;

public abstract class ZObject {
  protected ZObject() {
    nativeHandle_ = 0;
    owningHandle_ = true;
  }

  protected ZObject(long handle) {
    nativeHandle_ = handle;
    owningHandle_ = true;
  }

  public final synchronized void dispose() {
    if (isOwningNativeHandle() && isInitialized()) {
      disposeInternal();
    }
    nativeHandle_ = 0;
    disownNativeHandle();
  }

  protected abstract void disposeInternal();

  protected void disownNativeHandle() {
    owningHandle_ = false;
  }

  protected boolean isOwningNativeHandle() {
    return owningHandle_;
  }

  protected boolean isInitialized() {
    return nativeHandle_ != 0;
  }

  public long handle() {
    return nativeHandle_;
  }

  @Override
  protected void finalize() throws Throwable {
    dispose();
    super.finalize();
  }

  protected long nativeHandle_;
  private boolean owningHandle_;
}
