package site.ycsb.db;

/**
 * CapybaraKV exception type.
 */
public class CapybaraKVException extends RuntimeException {
  public CapybaraKVException(String errorMessage) {
      super(errorMessage);
  }
}
