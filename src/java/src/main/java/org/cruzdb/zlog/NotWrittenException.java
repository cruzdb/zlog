package org.cruzdb.zlog;

/**
 * Signals that a log position has not been written.
 *
 * This exception is thrown when a log position that has not been written to
 * is read.
 */
public class NotWrittenException extends LogException {
  public NotWrittenException(final String msg) {
    super(msg);
  }
}
