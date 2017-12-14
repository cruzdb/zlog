package org.cruzdb.zlog;

import java.util.Random;
import java.util.HashMap;

import static org.junit.Assert.*;
import org.junit.*;
import static org.assertj.core.api.Assertions.assertThat;

public class LogTest {

  // LogException is thrown when the Log cannot be created
  //@Test(expected=LogException.class)
  //public void openThrows() throws LogException {
  //  Random rand = new Random();
  //  String logname = "" + rand.nextInt();
  //  Log log = Log.openLMDB(logname);
  //  //Log log = Log.openLMDB("xyz", "abc", 5678, logname);
  //}

  private Log getLog() throws LogException {
    HashMap<String, String> opts = new HashMap<String, String>();
    opts.put("path", "db");

    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("lmdb", opts, logname);

    return log;
  }

  @Test(expected=NullPointerException.class)
  public void appendNullAppend() throws LogException {
    Log log = getLog();
    log.append(null);
  }

  @Test
  public void append() throws LogException {
    Log log = getLog();
    long first_pos = log.append(new byte[20]);
    long pos = log.append(new byte[20]);
    assertEquals(pos, first_pos+1);
    pos = log.append(new byte[20]);
    assertEquals(pos, first_pos+2);
  }

  @Test(expected=NotWrittenException.class)
  public void readNotWritten() throws LogException {
    Log log = getLog();
    log.read(20);
  }

  @Test(expected=FilledException.class)
  public void readFilled() throws LogException {
    Log log = getLog();
    log.fill(20);
    log.read(20);
  }

  @Test
  public void read() throws LogException {
    Log log = getLog();
    byte[] indata = "this is the input".getBytes();
    long pos = log.append(indata);
    byte[] outdata = log.read(pos);
    assertArrayEquals(indata, outdata);
  }

  @Test(expected=ReadOnlyException.class)
  public void fillReadOnly() throws LogException {
    Log log = getLog();
    long pos = log.append("asdf".getBytes());
    log.fill(pos);
  }

  @Test
  public void fill() throws LogException {
    Log log = getLog();
    log.fill(33);
  }

  @Test
  public void trim() throws LogException {
    Log log = getLog();
    log.trim(33);
    long pos = log.append("asdf".getBytes());
    log.trim(pos);
  }

  @Test
  public void tail() throws LogException {
    Log log = getLog();
    long pos = log.tail();
    assertEquals(pos, 0);
    pos = log.tail();
    assertEquals(pos, 0);
    long pos2 = log.append("asdf".getBytes());
    pos = log.tail();
    assertEquals(pos, pos2+1);
  }
}
