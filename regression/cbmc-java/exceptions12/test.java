class A extends RuntimeException {}
class B extends A {}
class C extends B {}

class F {
  void foo() {
    try {
      B b = new B();
      throw b;
    }
    catch(B exc) {
      assert false;
    }
  }
}

public class test {
  public static void main (String args[]) {
    try {
      F f = new F();
      f.foo();
    }
    catch(B exc) {
      assert false;
    }
  }
}
