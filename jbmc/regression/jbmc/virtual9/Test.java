public class Test {
  public static void runF(A x) {
    x.f();
  }

  public static void main(String[] args) {
    A y = null;
    if(args.length==3)
      y = new C();
    else
      y = new E();
    runF(y);
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
