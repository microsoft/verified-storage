package site.ycsb.db;

import static java.nio.charset.StandardCharsets.UTF_8;

/** 
 * Java wrapper for Viper instance.
 */
public class Viper {

  private static native long ViperCreate(byte[] poolFile, long initSize);

  // private static native boolean ViperPut(long kvPtr, byte[] key, byte[] values);

  // private static native boolean ViperUpdate(long kvPtr, byte[] key, byte[] values);

  // private static native boolean ViperRead(long kvPtr, byte[] key, byte[] values);

  private static native void ViperCleanup(long kvPtr);

  private long kvPtr;

  public long getPtr() {
    return this.kvPtr;
  }

  static {
    // System.loadLibrary("pthread");
    // TODO: don't hardcode path
    System.load("/mnt/local_ssd/usr/lib/x86_64-linux-gnu/libpthread.so");
    System.loadLibrary("viper_wrapper");
    System.loadLibrary("benchmark");
  }

  public Viper(String poolFile, long initSize) {
    System.out.println("creating viper");
    byte[] viperPoolFile = poolFile.getBytes(UTF_8);
    kvPtr = Viper.ViperCreate(viperPoolFile, initSize);
  }

  // public boolean insert(String key, byte[] values) {
  //   byte[] keyArray = key.getBytes(UTF_8);
  //   return Viper.ViperPut(kvPtr, keyArray, values);
  // }

  // public boolean update(String key, byte[] values) {
  //   byte[] keyArray = key.getBytes(UTF_8);
  //   return Viper.ViperUpdate(kvPtr, keyArray, values);
  // }

  // public byte[] read(String key, byte[] values) {
  //   byte[] keyArray = key.getBytes(UTF_8);
  //   Viper.ViperRead(kvPtr, keyArray, values);
  //   return values;
  // }

  public void cleanup() {
    System.out.println("viper cleanup");
    Viper.ViperCleanup(kvPtr);
  }
}