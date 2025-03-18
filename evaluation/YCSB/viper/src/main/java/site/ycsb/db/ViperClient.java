package site.ycsb.db;

import site.ycsb.*;

import site.ycsb.ByteArrayByteIterator;
import site.ycsb.ByteIterator;
import site.ycsb.DB;
import site.ycsb.DBException;
import site.ycsb.Status;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
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
  static final long INITIAL_SIZE = 1073741824;

  Viper db;

  @Override
  public void init() throws DBException {
    System.out.println("viper init");
    db = new Viper(POOL_FILE, INITIAL_SIZE);
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
      db.insert(key, serializedValues);
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
      byte[] serializedValues = serializeValues(values);
      db.update(key, serializedValues);
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
    try {
      // this is kind of annoying/inefficient, but Viper requires us to pass in the destination for 
      // the read. The easiest place to allocate that is here and the easiest way to do that is 
      // to serialize `result`, which should already have the correct size.
      byte[] values = serializeValues(result);
      db.read(key, values);
      deserializeValues(values, fields, result);
      return Status.OK;
    } catch (IOException e) {
      LOGGER.error(e.getMessage(), e);
      System.out.println("error on read key " + key);
      return Status.ERROR;
    }
  }

  @Override
  public void cleanup() {
    db.cleanup();
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

}