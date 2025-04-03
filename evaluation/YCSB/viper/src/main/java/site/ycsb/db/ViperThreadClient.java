package site.ycsb.db;

import static java.nio.charset.StandardCharsets.UTF_8;

public class ViperThreadClient {

    private static native long ViperGetClient(long kvPtr);

    private static native boolean ViperPut(long clientPtr, byte[] key, byte[] values);

    private static native boolean ViperUpdate(long clientPtr, byte[] key, byte[] values);

    private static native boolean ViperRead(long clientPtr, byte[] key, byte[] values);

    private static native void ViperClientCleanup(long clientPtr);

    private long clientPtr;

    static {
        // System.loadLibrary("pthread");
        // TODO: don't hardcode path
        System.load("/mnt/local_ssd/usr/lib/x86_64-linux-gnu/libpthread.so");
        System.loadLibrary("viper_wrapper");
        System.loadLibrary("benchmark");
    }

    public ViperThreadClient(Viper db) {
        clientPtr = ViperThreadClient.ViperGetClient(db.getPtr());
    }

    public boolean insert(String key, byte[] values) {
        byte[] keyArray = key.getBytes(UTF_8);
        return ViperThreadClient.ViperPut(clientPtr, keyArray, values);
    }

    public boolean update(String key, byte[] values) {
        byte[] keyArray = key.getBytes(UTF_8);
        return ViperThreadClient.ViperUpdate(clientPtr, keyArray, values);
    }

    public byte[] read(String key, byte[] values) {
        byte[] keyArray = key.getBytes(UTF_8);
        ViperThreadClient.ViperRead(clientPtr, keyArray, values);
        return values;
    }

    public void cleanup() {
        ViperThreadClient.ViperClientCleanup(clientPtr);
    }
}

