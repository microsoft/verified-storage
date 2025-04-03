package site.ycsb.db;

import static java.nio.charset.StandardCharsets.UTF_8;

/** 
 * Java wrapper for Viper instance.
 */
public class Viper {

  private static native long ViperCreate(byte[] poolFile, long initSize);

  private static native void ViperCleanup(long kvPtr);

  private long kvPtr;

  public long getPtr() {
    return this.kvPtr;
  }

  static {
    System.loadLibrary("pthread");
    System.loadLibrary("viper_wrapper");
    System.loadLibrary("benchmark");
  }

  public Viper(String poolFile, long initSize) {
    System.out.println("creating viper");
    byte[] viperPoolFile = poolFile.getBytes(UTF_8);
    kvPtr = Viper.ViperCreate(viperPoolFile, initSize);
  }

  public void cleanup() {
    System.out.println("viper cleanup");
    Viper.ViperCleanup(kvPtr);
  }
}