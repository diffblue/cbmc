import org.cprover.CProver;

class ObjectWithNondetInitialize {
  private int value_;
  public void cproverNondetInitialize() {
    CProver.assume(value_ == 13);
  }
  public int value() {
    return value_;
  }
}
