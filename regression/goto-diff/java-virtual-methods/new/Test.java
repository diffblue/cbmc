class A {
  boolean bar() {
    return true;
  }
}

class B extends A {
  boolean bar() {
    return false;
  }
}

public class Test {

  public boolean foo(A x) {
    return x.bar();
  }
}
