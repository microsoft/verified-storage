package site.ycsb.workloads;

import site.ycsb.*;
import site.ycsb.generator.*;
import site.ycsb.measurements.Measurements;

import java.util.*;

/**
 * Workload class for storage node workloads from traces.
 */
public class TraceWorkload extends Workload {
    /**
   * The name of the property for the proportion of transactions that are reads.
   */
  public static final String READ_PROPORTION_PROPERTY = "readproportion";

  /**
   * The name of the property for the proportion of transactions that are updates.
   */
  public static final String UPDATE_PROPORTION_PROPERTY = "updateproportion";

  /**
   * The name of the property for the proportion of transactions that are inserts.
   */
  public static final String INSERT_PROPORTION_PROPERTY = "insertproportion";

  /**
   * The name of the property for the the distribution of requests across the keyspace. Options are
   * "uniform", "zipfian" and "latest"
   */
  public static final String REQUEST_DISTRIBUTION_PROPERTY = "requestdistribution";

  protected DiscreteGenerator operationchooser;
  protected NumberGenerator keychooser;

  private Measurements measurements = Measurements.getMeasurements();

  /**
   * Initialize the scenario.
   * Called once, in the main client thread, before any operations are started.
   */
  @Override
  public void init(Properties p) throws WorkloadException {

  }

  /**
   * Do one insert operation.
   */
  @Override 
  public boolean doInsert(DB db, Object threadstate) {
    return false;
  }

  /**
   * Do one transaction operation.
   */
  @Override
  public boolean doTransaction(DB db, Object threadstate) {
    return false;
  }
}
