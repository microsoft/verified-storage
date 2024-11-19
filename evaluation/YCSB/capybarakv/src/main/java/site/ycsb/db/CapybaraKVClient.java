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
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
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

  static final String PROPERTY_CONFIG_FILE = "capybarakv.configfile";
  @GuardedBy("CapybaraKVClient.class") private static String configFile = null;
  
  private static final Logger LOGGER = LoggerFactory.getLogger(CapybaraKVClient.class);

  // maps shard IDs to the corresponding KV
  // TODO: a more idiomatic approach would be to have a thread pool where each 
  // thread handles one KV, but that might interact strangely with 
  // the incoming YCSB-created threads, so let's try a slightly simpler approach first.
  // TODO: should these be volatile? final?
  private static volatile ConcurrentMap<Long, CapybaraKV> kvMap = new ConcurrentHashMap<>();
  private static volatile ConcurrentMap<Long, Lock> kvLockMap = new ConcurrentHashMap<>();

  private static AtomicInteger counter = new AtomicInteger(0);

  @Override
  public void init() throws DBException {
    System.err.println("Init CapybaraKV");
    synchronized(CapybaraKVClient.class) {
      if (configFile == null) {
        configFile = getProperties().getProperty(PROPERTY_CONFIG_FILE);
        if (configFile == null) {
          String message = "Please provide a config file.";
          throw new DBException(message);
        }  
      }
    }
    initCapybaraKV();
    System.err.println("Done init CapybaraKV");
  }

  private void initCapybaraKV() throws DBException {
    long id = Long.valueOf(counter.getAndAdd(1));
    CapybaraKV kv = new CapybaraKV(configFile, id);
    Lock lock = new ReentrantLock();
    kvMap.put(id, kv);
    kvLockMap.put(id, lock);
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
      long id = getShardId(key);
      CapybaraKV kv = kvMap.get(id);
      Lock lock = kvLockMap.get(id);
      lock.lock();
      kv.insert(table, key, serializedValues);
      kv.commit();
      lock.unlock();
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
      long id = getShardId(key);
      CapybaraKV kv = kvMap.get(id);
      Lock lock = kvLockMap.get(id);

      lock.lock();
      // read the current value at this key
      byte[] currentValue = kv.read(table, key);
      final Map<String, ByteIterator> result = new HashMap<>();
      deserializeValues(currentValue, null, result);
      // update the result with the new fields
      result.putAll(values);
      // serialize the updated value to bytes
      byte[] updateBytes = serializeValues(result);
      kv.update(table, key, updateBytes);
      kv.commit();
      lock.unlock();
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
      long id = getShardId(key);
      CapybaraKV kv = kvMap.get(id);
      Lock lock = kvLockMap.get(id);
      lock.lock();
      byte[] values = kv.read(table, key);
      deserializeValues(values, fields, result);
      lock.unlock();
      return Status.OK;
    } catch(CapybaraKVException e) {
      LOGGER.error(e.getMessage(), e);
      return Status.ERROR;
    }
  }

  @Override 
  public void cleanup() throws DBException {
    synchronized(CapybaraKVClient.class) {
      if (kvMap != null) {
        System.out.println("Cleaning up");
        for (long id = 0; id < counter.get(); id++) {
          CapybaraKV kv = kvMap.get(id);
          Lock lock = kvLockMap.get(id);
          lock.lock();
          kv.cleanup();
          lock.unlock();
        }
        kvMap = null;
        kvLockMap = null;
      }
      
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

  private long getShardId(String key) {
    // TODO: is this hashing approach acceptable?
    long hash = Math.abs(Long.valueOf(key.hashCode()));
    // the counter tells us how many shards there are
    long id = hash % Long.valueOf(counter.get());
    return id;
  }
}
