package site.ycsb.db;

import static java.nio.charset.StandardCharsets.UTF_8;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Java wrapper for CapybaraKV object.
 */
public class CapybaraKV {

  private static final Logger LOGGER = LoggerFactory.getLogger(CapybaraKV.class);

  private static native long kvInit();
  private static native void kvCleanup(long kvPtr);
  private static native void kvInsert(long kvPtr, byte[] table, 
      byte[] key, byte[] value);
  private static native byte[] kvRead(long kvPtr, byte[] table, byte[] key);

  private long kvPtr;

  static {
    System.loadLibrary("ycsb_ffi");
  }

  public CapybaraKV() {
    kvPtr = CapybaraKV.kvInit();
  }

  // this should throw an exception on failure rather than returning err?
  public void insert(String table, String key, byte[] values) throws CapybaraKVException {
    byte[] tableArray = table.getBytes(UTF_8);
    byte[] keyArray = key.getBytes(UTF_8);

    CapybaraKV.kvInsert(kvPtr, tableArray, keyArray, values);
  }

  public byte[] read(String table, String key) throws CapybaraKVException {
    byte[] tableArray = table.getBytes(UTF_8);
    byte[] keyArray = key.getBytes(UTF_8);

    byte[] ret = CapybaraKV.kvRead(kvPtr, tableArray, keyArray);
    return ret;
  }

  public void cleanup() {
    CapybaraKV.kvCleanup(kvPtr);
  }
}
