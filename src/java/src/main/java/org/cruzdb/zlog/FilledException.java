package org.cruzdb.zlog;

/**
 * Signals that a log position has been filled or invalidated.
 *
 * This exception is thrown when a log position that has been filled or
 * invalidated is read.
 */
public class FilledException extends LogException {
  public FilledException(final String msg) {
    super(msg);
  }
}
