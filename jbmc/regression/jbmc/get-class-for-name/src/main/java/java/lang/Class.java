package java.lang;

// A minimal model of java.lang.Class with unique Class objects per name, which
// provides cproverGetClassObject for JBMC's implementation of getClass.
public class Class<T> {
  private String name;
  private boolean cproverIsEnum;
  private Class<?> cproverNextClass;

  // Class literals that JBMC initialises in __CPROVER_initialize
  private static final Class<?>[] literals = new Class<?>[1];
  // Class objects created by forName or cproverGetClassObject
  private static final Class<?>[] others = new Class<?>[1];

  public String getName() { return name; }
  public boolean isEnum() { return cproverIsEnum; }
  public boolean desiredAssertionStatus() { return true; }

  private static Class<?> findOther(String name) {
    for (Class<?> c = others[0]; c != null; c = c.cproverNextClass)
      if (name.equals(c.name))
        return c;
    return null;
  }

  private static Class<?> newOther(String name) {
    Class<?> c = new Class<>();
    c.name = name;
    c.cproverNextClass = others[0];
    others[0] = c;
    return c;
  }

  public static Class<?> forName(String name) {
    for (Class<?> c = literals[0]; c != null; c = c.cproverNextClass)
      if (name.equals(c.name))
        return c;
    Class<?> c = findOther(name);
    return c != null ? c : newOther(name);
  }

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
    this.cproverIsEnum = isEnum;
    cproverNextClass = literals[0];
    literals[0] = this;
  }

  @org.cprover.MustNotThrow
  private static Class<?> cproverGetClassObject(
    String name,
    boolean isAnnotation,
    boolean isArray,
    boolean isInterface,
    boolean isSynthetic,
    boolean isLocalClass,
    boolean isMemberClass,
    boolean isEnum) {
    Class<?> c = findOther(name);
    if (c == null)
      c = newOther(name);
    c.cproverIsEnum = isEnum;
    return c;
  }
}
