class A {
}

class B extends A {
}

public class Test {

  public boolean foo(A x) {
    if (x instanceof A) {
      return true;
    } else {
      return false;
    }
  }
}
