package site.ycsb.db;

import site.ycsb.Status;

import static java.nio.charset.StandardCharsets.UTF_8;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Java wrapper for CapybaraKV object.
 */
public class CapybaraKV {

  // TODO: make configurable
  private int maxKeySize = 1024;
  private int maxValueSize = 1140;

  private static final Logger LOGGER = LoggerFactory.getLogger(CapybaraKV.class);

  private static native long kvInit();
  private static native void kvCleanup(long kvPtr);
  private static native int kvInsert(long kvPtr, byte[] table, 
      byte[] key, byte[] value);

  private long kvPtr;

  static {
    System.loadLibrary("ycsb_ffi");
  }

  public CapybaraKV() {
    kvPtr = CapybaraKV.kvInit();
  }

  // this should throw an exception on failure rather than returning err?
  public Status insert(String table, String key, byte[] values) {
    byte[] tableArray = table.getBytes(UTF_8);
    byte[] keyArray = key.getBytes(UTF_8);

    if (keyArray.length > maxKeySize) {
      LOGGER.error("Key " + key + " is too big (length " + keyArray.length +
          ", max length " + maxKeySize + ")");
      return Status.BAD_REQUEST;
    }
    if (values.length > maxValueSize) {
      LOGGER.error("Item for " + key + " is too big (length " + values.length +
          ", max length " + maxValueSize + ")");
      return Status.BAD_REQUEST;
    }
    int ret = CapybaraKV.kvInsert(kvPtr, tableArray, keyArray, values);
    if (ret < 0) {
      return Status.ERROR;
    } else {
      return Status.OK;
    }
  }

  public void cleanup() {
    CapybaraKV.kvCleanup(kvPtr);
  }
}
