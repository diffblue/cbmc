public class Test {
  static class A {}
  static class B {}
  static class C {}
  enum E { X }

  public static void forNameThenGetClass() {
    Class<?> c = Class.forName("Test$A");
    assert new A().getClass() == c;
    assert Class.forName("Test$A") == c;
  }

  public static void getClassThenForName() {
    Class<?> c = new A().getClass();
    assert Class.forName("Test$A") == c;
  }

  public static void classLiteral() {
    assert Class.forName("Test$C") == C.class;
    assert new C().getClass() == C.class;
  }

  public static void twoClasses() {
    Class<?> a = Class.forName("Test$A");
    Class<?> b = Class.forName("Test$B");
    assert new B().getClass() == b;
    assert new A().getClass() == a;
    assert a != b;
  }

  public static void firstCallOnBranch(boolean nondet) {
    if (nondet)
      new A().getClass();
    Class<?> c = new A().getClass();
    assert Class.forName("Test$A") == c;
  }

  public static void enumFlag() {
    Class<?> c = Class.forName("Test$E");
    assert E.X.getClass() == c;
    assert c.isEnum();
  }

  public static void objectReceiver() {
    Object o = new Object();
    assert o.getClass() == Object.class;
    assert new Object().getClass() == o.getClass();
    Object a = new A();
    assert a.getClass() != o.getClass();
  }

  public static void mustFail() {
    Class<?> c = Class.forName("Test$A");
    assert new B().getClass() == c;
  }
}
