public class test {
  public static void main() {
    A[] as = { new A(), new B(), new C(), new D(), new E() };
    as[2].f();
  }
}

class A {
  void f() { }
}


class B extends A {
  void f() { }
}

class C extends A {
  void f() { }
}

class D extends C {
}

class E extends B {
}
