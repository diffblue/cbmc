package java.lang;

public class Class {

  private String name;

  private boolean isAnnotation;
  private boolean isArray;
  private boolean isInterface;
  private boolean isSynthetic;
  private boolean isLocalClass;
  private boolean isMemberClass;
  private boolean isEnum;

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
    this.isAnnotation = isAnnotation;
    this.isArray = isArray;
    this.isInterface = isInterface;
    this.isSynthetic = isSynthetic;
    this.isLocalClass = isLocalClass;
    this.isMemberClass = isMemberClass;
    this.isEnum = isEnum;

  }

  public String getName() { return name; }

  public boolean isAnnotation() { return isAnnotation; }
  public boolean isArray() { return isArray; }
  public boolean isInterface() { return isInterface; }
  public boolean isSynthetic() { return isSynthetic; }
  public boolean isLocalClass() { return isLocalClass; }
  public boolean isMemberClass() { return isMemberClass; }
  public boolean isEnum() { return isEnum; }
}
