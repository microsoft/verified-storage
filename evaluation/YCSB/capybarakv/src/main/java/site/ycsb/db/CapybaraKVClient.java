package site.ycsb.db;

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
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * YCSB binding for CapybaraKV.
 */
public class CapybaraKVClient extends DB {

  private CapybaraKV kv;  
  
  private static final Logger LOGGER = LoggerFactory.getLogger(CapybaraKVClient.class);

  @Override
  public void init() throws DBException {
    initCapybaraKV();
  }

  private void initCapybaraKV() throws DBException {
    kv = new CapybaraKV();
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
      kv.commit();
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
    kv.cleanup();
  }

  // These functions are borrowed from RocksDBClient.java
  // FIXME: you are only given a subset of fields to update! This is why this function isn't 
  // working. Need to read the item, update it according to the new fields in the argument, and 
  // then write THAT. that has to happen here in the client
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
}
