package org.cruzdb.zlog;

/**
 * Signals that a zlog error has occurred.
 *
 * This exception is used to describe an internal error from the C++ zlog
 * library.
 */
public class LogException extends Exception {
  public LogException(final String msg) {
    super(msg);
  }
}
