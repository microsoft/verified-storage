package site.ycsb.db;

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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * YCSB binding for CapybaraKV.
 */
public class CapybaraKVClient extends DB {

  static final String PROPERTY_CAPYBARAKV_CONFIG_FILE = "capybarakv.configfile";
  static final String PROPERTY_EXP_CONFIG_FILE = "experiment.configfile";
  @GuardedBy("CapybaraKVClient.class") private static String capybarakvConfigFile = null;
  @GuardedBy("CapybaraKVClient.class") private static String experimentConfigFile = null;
  
  private static final Logger LOGGER = LoggerFactory.getLogger(CapybaraKVClient.class);

  private static long preAvailableMem = 0;
  private static long postAvailableMem = 0;

  private static volatile CapybaraKV kv = null;

  private static AtomicInteger counter = new AtomicInteger(0);

  @Override
  public void init() throws DBException {
    synchronized(CapybaraKVClient.class) {
      if (preAvailableMem == 0) {
        preAvailableMem = getAvailableMem();
        System.out.println("Pre-experiment available mem: " + preAvailableMem);
      }
      if (capybarakvConfigFile == null) {
        capybarakvConfigFile = getProperties().getProperty(PROPERTY_CAPYBARAKV_CONFIG_FILE);
        if (capybarakvConfigFile == null) {
          String message = "Please provide a CapybaraKV config file.";
          throw new DBException(message);
        }  
      }
      if (experimentConfigFile == null) {
        experimentConfigFile = getProperties().getProperty(PROPERTY_EXP_CONFIG_FILE);
        if (experimentConfigFile == null) {
          String message = "Please provide an experiment config file.";
          throw new DBException(message);
        }
      }
      if (kv == null) {
        initCapybaraKV();
      }
      counter.addAndGet(1);
    }
  }

  private void initCapybaraKV() throws DBException {
    kv = new CapybaraKV(capybarakvConfigFile, experimentConfigFile);
  }

  @Override
  public Status delete(String table, String key) {
    return Status.ERROR;
  }

  // NOTE: ByteIterator is a YCSB-local class and acts like a stream.
  // If you do anything with it (even just printing its contents) it 
  // is consumed.
  @Override
  public Status insert(String table, String key,
      Map<String, ByteIterator> values) {
    try {
      byte[] serializedValues = serializeValues(values);
      kv.insert(table, key, serializedValues);
      return Status.OK;
    } catch(IOException | CapybaraKVException e) {
      LOGGER.error(e.getMessage(), e);
      System.out.println("error on key " + key);
      return Status.ERROR;
    }
  }

  @Override
  public Status update(String table, String key,
      Map<String, ByteIterator> values) {
    try {
      // serialize the updated value to bytes
      byte[] updateBytes = serializeValues(values);
      kv.update(table, key, updateBytes);
      return Status.OK;
    } catch(IOException | CapybaraKVException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override
  public Status scan(String table, String startkey, int recordcount,
      Set<String> fields, Vector<HashMap<String, ByteIterator>> result) {
    // Not supported
    return Status.ERROR;
  }

  @Override
  public Status read(String table, String key, Set<String> fields,
      Map<String, ByteIterator> result) {
    try {
      byte[] values = kv.read(table, key);
      deserializeValues(values, fields, result);
      return Status.OK;
    } catch(CapybaraKVException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override 
  public void cleanup() throws DBException {
    synchronized(CapybaraKVClient.class) {
      if (counter.get() == 1) {
        // If all threads but one have called cleanup, we can clean up 
        // the actual KV store
        postAvailableMem = getAvailableMem();
        System.out.println("Post-experiment available mem: " + postAvailableMem);
        System.out.println("Mem usage: " + (preAvailableMem - postAvailableMem));
        kv.cleanup();
        kv = null;
      }
      counter.decrementAndGet();
    }
  }

  // These functions are borrowed from RocksDBClient.java
  private Map<String, ByteIterator> deserializeValues(final byte[] values, final Set<String> fields,
      final Map<String, ByteIterator> result) {
    final ByteBuffer buf = ByteBuffer.allocate(4);

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
