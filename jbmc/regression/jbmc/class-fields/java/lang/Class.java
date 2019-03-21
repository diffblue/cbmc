package java.lang;

public class Class {

  public Integer field;

  @org.cprover.MustNotThrow
  protected void cproverNondetInitialize() {
    org.cprover.CProver.assume(field == null);
  }

}
