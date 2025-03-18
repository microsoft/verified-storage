package site.ycsb.db;

import static java.nio.charset.StandardCharsets.UTF_8;

/** 
 * Java wrapper for Viper instance.
 */
public class Viper {

  private static native long ViperCreate(byte[] poolFile, long initSize);

  private static native boolean ViperPut(long kvPtr, byte[] key, byte[] values);

  private static native boolean ViperUpdate(long kvPtr, byte[] key, byte[] values);

  private static native boolean ViperRead(long kvPtr, byte[] key, byte[] values);

  private static native void ViperCleanup(long kvPtr);

  private long kvPtr;

  static {
    System.loadLibrary("viper_wrapper");
  }

  public Viper(String poolFile, long initSize) {
    byte[] viperPoolFile = poolFile.getBytes(UTF_8);
    kvPtr = Viper.ViperCreate(viperPoolFile, initSize);
  }

  public boolean insert(String key, byte[] values) {
    byte[] keyArray = key.getBytes(UTF_8);
    return Viper.ViperPut(kvPtr, keyArray, values);
  }

  public boolean update(String key, byte[] values) {
    byte[] keyArray = key.getBytes(UTF_8);
    return Viper.ViperUpdate(kvPtr, keyArray, values);
  }

  public byte[] read(String key, byte[] values) {
    byte[] keyArray = key.getBytes(UTF_8);
    Viper.ViperRead(kvPtr, keyArray, values);
    return values;
  }

  public void cleanup() {
    Viper.ViperCleanup(kvPtr);
  }
}