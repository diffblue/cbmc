class B {
  void foo() {}
}

class A {
  B b = new B();
}

public class Test {
  public A f00(A x) {
    return org.cprover.CProver.nondetWithoutNull();
  }

  public A f01(A z) {
    return org.cprover.CProver.nondetWithoutNull();
  }
}
