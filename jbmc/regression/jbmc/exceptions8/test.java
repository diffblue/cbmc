class A extends RuntimeException {}
class B extends A {}
class C extends B {}

public class test {
  static void foo() {
    try {
      B b = new B();
      throw b;
    }
    catch(C exc) {
      int i=0;
    }
  }
  
  public static void main (String args[]) {
    try {
      A a = new A();
      foo();
      throw a;
    }
    catch(B exc) {
      assert false;
    }
    catch(A exc) {
      assert false;
    }
  }
}
