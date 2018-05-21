public class VirtualFunctions {
  Object static_object;

  public static class A {
    public void f() {
    }
  }

  public static class B extends A{
    public void f() {
    }
  }

  public static class C extends B {
  }

  public static void check(A a, B b, C c) {
    // multiple possibilities, one needs a cast
    a.f();

    // single possibility, does not need a cast
    b.f();

    // single possibility, needs cast
    c.f();
  }
}
