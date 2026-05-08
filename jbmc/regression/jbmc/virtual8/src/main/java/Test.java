public class Test {
  public static void runF(A x) {
    x.f();
  }

  public static void main() {
    A y = new D();
    runF(y);
  }
}

class A {
  int f() { return 0; }
}


class B extends A {
  int f() { return 0; }
}

class C extends A {
  int f() { return 0; }
}

class D extends C {
}

class E extends B {
}
