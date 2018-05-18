package java.lang;

public class Class {

  public Integer field;

  protected void cproverNondetInitialize() {
    org.cprover.CProver.assume(field == null);
  }

}
