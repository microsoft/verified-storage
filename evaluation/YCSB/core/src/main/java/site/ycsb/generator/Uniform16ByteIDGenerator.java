package site.ycsb.generator;

import java.nio.ByteBuffer;

/**
 * 16-byte ID generator.
 * In practice, these are UUIDs, but because YCSB expects to pick keys uniformly
 * from a known range, we won't use actual UUIDs.
 * The returned value will be 16-byte byte arrays to match the key type expected
 * by our DBs.
 * 8 of these bytes will be set to 0 to keep things simple.
 * 
 * We extend Generator, rather than an existing uniform generator class,
 * so that we we can return byte arrays here; we use the UniformLongGenerator
 * class to do the actual generation.
 */
public class Uniform16ByteIDGenerator extends Generator {
  private UniformLongGenerator longgenerator;
  private byte[] lastval;

  public Uniform16ByteIDGenerator(long lb, long ub) {
    this.longgenerator = new UniformLongGenerator(lb, ub);
  }

  @Override
  public byte[] nextValue() {
    long val1 = longgenerator.nextValue();
    long val2 = 0;
    byte[] ret = longsToBytes(val1, val2);
    this.lastval = ret;
    return ret;
  }

  @Override
  public byte[] lastValue() {
    return this.lastval;
  }

  // https://stackoverflow.com/questions/4485128/how-do-i-convert-long-to-byte-and-back-in-java
  private byte[] longsToBytes(long val1, long val2) {
    ByteBuffer buffer = ByteBuffer.allocate(Long.BYTES * 2);
    buffer.putLong(val1);
    buffer.putLong(val2);
    return buffer.array();
  }
}