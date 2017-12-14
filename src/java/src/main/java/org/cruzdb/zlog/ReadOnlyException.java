package org.cruzdb.zlog;

/**
 * Signals that a log position cannot be written.
 *
 * This is thrown when a log position that has been written is filled or
 * invalidated.
 */
public class ReadOnlyException extends LogException {
  public ReadOnlyException(final String msg) {
    super(msg);
  }
}
