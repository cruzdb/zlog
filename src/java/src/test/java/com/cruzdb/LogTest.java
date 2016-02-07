package com.cruzdb;

import java.util.Random;

import static org.junit.Assert.*;
import org.junit.*;

public class LogTest {

  // LogException is thrown when the Log cannot be created
  @Test(expected=LogException.class)
  public void openThrows() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("xyz", "abc", 5678, logname);
  }

  @Test(expected=NullPointerException.class)
  public void appendNullAppend() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    log.append(null);
  }

  @Test
  public void append() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    long pos = log.append(new byte[20]);
    assertEquals(pos, 0); // first append
    pos = log.append(new byte[20]);
    assertEquals(pos, 1);
    pos = log.append(new byte[20]);
    assertEquals(pos, 2);
  }

  @Test(expected=NotWrittenException.class)
  public void readNotWritten() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    log.read(20);
  }

  @Test(expected=FilledException.class)
  public void readFilled() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    log.fill(20);
    log.read(20);
  }

  @Test
  public void read() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    byte[] indata = "this is the input".getBytes();
    long pos = log.append(indata);
    byte[] outdata = log.read(pos);
    assertArrayEquals(indata, outdata);
  }

  @Test(expected=ReadOnlyException.class)
  public void fillReadOnly() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    long pos = log.append("asdf".getBytes());
    log.fill(pos);
  }

  @Test
  public void fill() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    log.fill(33);
  }

  @Test
  public void trim() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    log.trim(33);
    long pos = log.append("asdf".getBytes());
    log.trim(pos);
  }

  @Test
  public void tail() throws LogException {
    Random rand = new Random();
    String logname = "" + rand.nextInt();
    Log log = Log.open("rbd", "localhost", 5678, logname);
    long pos = log.tail();
    assertEquals(pos, 0);
    pos = log.tail();
    assertEquals(pos, 0);
    long pos2 = log.append("asdf".getBytes());
    assertEquals(pos2, 0);
    pos = log.tail();
    assertEquals(pos, 1);
  }
}
