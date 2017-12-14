package org.cruzdb.zlog;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;

/**
 *
 */
public class NativeLibraryLoader {
  private static final NativeLibraryLoader instance = new NativeLibraryLoader();
  private static boolean initialized = false;

  private static final String sharedLibraryName = "zlogjni";
  private static final String jniLibraryFileName = "libzlogjni.so";
  private static final String tempFilePrefix = "libzlogjni";
  private static final String tempFileSuffix = ".so";

  public static NativeLibraryLoader getInstance() {
    return instance;
  }

  private NativeLibraryLoader() {}

  public synchronized void loadLibrary(final String tmpDir) throws IOException {
    try {
      System.loadLibrary(sharedLibraryName);
    } catch (final UnsatisfiedLinkError ule1) {
      loadLibraryFromJar(tmpDir);
    }
  }

  void loadLibraryFromJar(final String tmpDir) throws IOException {
    if (!initialized) {
      System.load(loadLibraryFromJarToTemp(tmpDir).getAbsolutePath());
      initialized = true;
    }
  }

  File loadLibraryFromJarToTemp(final String tmpDir) throws IOException {
    final File temp;
    if (tmpDir == null || tmpDir.isEmpty()) {
      temp = File.createTempFile(tempFilePrefix, tempFileSuffix);
    } else {
      temp = new File(tmpDir, jniLibraryFileName);
      if (!temp.createNewFile()) {
        throw new RuntimeException("File: " + temp.getAbsolutePath()
            + " could not be created.");
      }
    }

    if (!temp.exists()) {
      throw new RuntimeException("File " + temp.getAbsolutePath() + " does not exist.");
    } else {
      temp.deleteOnExit();
    }

    // attempt to copy the library from the Jar file to the temp destination
    try (final InputStream is = getClass().getClassLoader().
        getResourceAsStream(jniLibraryFileName)) {
      if (is == null) {
        throw new RuntimeException(jniLibraryFileName + " was not found inside JAR.");
      } else {
        Files.copy(is, temp.toPath(), StandardCopyOption.REPLACE_EXISTING);
      }
    }

    return temp;
  }
}
