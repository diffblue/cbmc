public class Test {
  static class A {
    int x;

    A(int x) {
      this.x = x;
    }

    @Override
    public boolean equals(Object o) {
      // a common idiom, which requires Class objects to be unique
      if(o == null || getClass() != o.getClass())
        return false;
      return x == ((A)o).x;
    }
  }

  static class B extends A {
    B(int x) {
      super(x);
    }
  }

  // no class literal of C appears in this program
  static class C {
  }

  public static void sameClass(int i) {
    A a1 = new A(i);
    A a2 = new A(i);
    assert a1.getClass() == a2.getClass();
    assert a1.equals(a2);
  }

  public static void classLiteral() {
    A a = new A(1);
    assert a.getClass() == A.class;
    assert a.getClass() != B.class;
  }

  public static void differentClass(int i) {
    A a = new A(i);
    B b = new B(i);
    assert a.getClass() != b.getClass();
    assert !a.equals(b);
  }

  public static void noClassLiteral() {
    Object c1 = new C();
    Object c2 = new C();
    assert c1.getClass() == c2.getClass();
    assert c1.getClass().getName().equals("Test$C");
  }

  public static void mustFail(int i) {
    A a = new A(i);
    B b = new B(i);
    assert a.getClass() == b.getClass();
  }
}
