package site.ycsb.db;

import site.ycsb.*;

import site.ycsb.ByteArrayByteIterator;
import site.ycsb.ByteIterator;
import site.ycsb.DB;
import site.ycsb.DBException;
import site.ycsb.Status;

import net.jcip.annotations.GuardedBy;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.io.BufferedReader;
import java.io.FileReader;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * YCSB binding for Viper.
 */
public class ViperClient extends DB {

  private static final Logger LOGGER = LoggerFactory.getLogger(ViperClient.class);

  // TODO: get these from a config file
  static final String POOL_FILE = "/mnt/pmem/viper";
  static final long INITIAL_SIZE = 64424509440L; // 60GB
  // static final int VALUE_SIZE = 1140; // TODO: don't hardcode this especially
  static final String PROPERTY_VIPER_VALUE_SIZE = "viper.valuesize";
  static final String PROPERTY_VIPER_INITIAL_POOL_SIZE = "viper.initialpoolsize";

  @GuardedBy("ViperClient.class") private static int references = 0;
  @GuardedBy("ViperClient.class") private static Viper db = null;
  private ViperThreadClient client = null;

  private static long preAvailableMem = 0;
  private static long postAvailableMem = 0;

  private static int value_size = 0;
  private static long pool_size = 0;

  byte[] value_buffer;

  @Override
  public void init() throws DBException {
    synchronized(ViperClient.class) {
      if (preAvailableMem == 0) {
        preAvailableMem = getAvailableMem();
        System.out.println("Pre-experiment available mem: " + preAvailableMem);
      }
      if (db == null) {
        System.out.println("viper init");
        String value_size_str = getProperties().getProperty(PROPERTY_VIPER_VALUE_SIZE);
        if (value_size_str == null) {
          value_size = 1140; // size used by default YCSB workloads
        } else {
          value_size = Integer.parseInt(value_size_str);
        }
        String pool_size_str = getProperties().getProperty(PROPERTY_VIPER_INITIAL_POOL_SIZE);
        if (pool_size_str == null) {
          pool_size = INITIAL_SIZE; // default size that works well for ycsb workloads
        } else {
          pool_size = Long.parseLong(pool_size_str);
        }
        db = new Viper(POOL_FILE, pool_size);
      }
      client = new ViperThreadClient(db);
      value_buffer = new byte[value_size];
      references++;
    }
  }

  // TODO: implement
  @Override
  public Status delete(String table, String key) {
    return Status.ERROR;
  }

  @Override
  public Status insert(String table, String key, Map<String, ByteIterator> values) {
    try {
      byte[] serializedValues = serializeValues(values);
      client.insert(key, serializedValues);
      return Status.OK;
    } catch (IOException e) {
      LOGGER.error(e.getMessage(), e);
      System.out.println("error on insert key " + key);
      return Status.ERROR;
    }
    
  }

  // TODO: this might need some work -- it did in Capybara
  @Override
  public Status update(String table, String key, Map<String, ByteIterator> values) {
    try {
      // // read the current value, update it, and write it back
      // byte[] readValues = new byte[value_size]; 
      // client.read(key, readValues);
      // Map<String, ByteIterator> result = new HashMap<>();
      // deserializeValues(readValues, null, result);
      // result.putAll(values);

      byte[] serializedValues = serializeValues(values);
      client.update(key, serializedValues);

      return Status.OK;
    } catch (IOException e) {
      LOGGER.error(e.getMessage(), e);
      System.out.println("error on update key " + key);
      return Status.ERROR;
    }
  }

  @Override
  public Status scan(String table, String startkey, int recordcount,
      Set<String> fields, Vector<HashMap<String, ByteIterator>> result) {
    // Not supported
    return Status.ERROR;
  }

  // TODO: this might need some work
  @Override
  public Status read(String table, String key, Set<String> fields, Map<String, ByteIterator> result) {
    // this is kind of annoying/inefficient, but Viper requires us to pass in the destination for 
    // the read. The easiest place to allocate that is here and the easiest way to do that is 
    // to serialize `result`, which should already have the correct size.
    // byte[] values = serializeValues(result);
    // byte[] values = new byte[value_size]; 
    client.read(key, value_buffer);
    deserializeValues(value_buffer, fields, result);
    return Status.OK;
  }

  @Override
  public void cleanup() {
    synchronized (ViperClient.class) {
      if (postAvailableMem == 0) {
        postAvailableMem = getAvailableMem();
        System.out.println("Post-experiment available mem: " + postAvailableMem);
        System.out.println("Mem usage: " + (preAvailableMem - postAvailableMem));
      }
      client.cleanup();
      if (references == 1) {
        System.out.println("cleaning up");
        db.cleanup();
        System.out.println("done cleaning up");
      }
      references--;
    }
  }

  // These functions are borrowed from RocksDBClient.java
  private Map<String, ByteIterator> deserializeValues(final byte[] values, final Set<String> fields,
      final Map<String, ByteIterator> result) {
    final ByteBuffer buf = ByteBuffer.allocate(4);

    // System.out.println(values.length);

    int offset = 0;
    while(offset < values.length) {
      buf.put(values, offset, 4);
      buf.flip();
      final int keyLen = buf.getInt();
      buf.clear();
      offset += 4;

      final String key = new String(values, offset, keyLen);
      offset += keyLen;

      // Stop when there are no more keys to deserialize
      if (keyLen == 0) {
        break;
      }

      buf.put(values, offset, 4);
      buf.flip();
      final int valueLen = buf.getInt();
      
      buf.clear();
      offset += 4;

      if(fields == null || fields.contains(key)) {
        result.put(key, new ByteArrayByteIterator(values, offset, valueLen));
      }

      offset += valueLen;
    }

    return result;
  }

  private byte[] serializeValues(final Map<String, ByteIterator> values) throws IOException {
    try(final ByteArrayOutputStream baos = new ByteArrayOutputStream()) {
      final ByteBuffer buf = ByteBuffer.allocate(4);

      for(final Map.Entry<String, ByteIterator> value : values.entrySet()) {
        final byte[] keyBytes = value.getKey().getBytes(UTF_8);
        final byte[] valueBytes = value.getValue().toArray();

        buf.putInt(keyBytes.length);
        baos.write(buf.array());
        baos.write(keyBytes);

        buf.clear();

        buf.putInt(valueBytes.length);
        baos.write(buf.array());
        baos.write(valueBytes);

        buf.clear();
      }
      return baos.toByteArray();
    }
  }

  private static long getAvailableMem() {
    try {
      BufferedReader memInfo = new BufferedReader(new FileReader("/proc/meminfo"));
      String line;
      while ((line = memInfo.readLine()) != null) {
        if (line.startsWith("MemAvailable: ")) {
          // Output is in KB which is close enough.
          return java.lang.Long.parseLong(line.split("[^0-9]+")[1]) * 1024;
        }
      }
    } catch (IOException e) {
      e.printStackTrace();
    }
    return -1;
  } 
}