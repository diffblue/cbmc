package java.lang;

public class Class<T> {

  private String name;

  @org.cprover.MustNotThrow
  public void cproverInitializeClassLiteral(
    String name,
    boolean isAnnotation,
    boolean isArray,
    boolean isInterface,
    boolean isSynthetic,
    boolean isLocalClass,
    boolean isMemberClass,
    boolean isEnum) {
    this.name = name;
    // a static field of another class, which must not be reset afterwards
    org.cprover.regression.ClassLiteralCounter.count[0]++;
  }

  public String getName() { return name; }

  public boolean desiredAssertionStatus() { return true; }
}
