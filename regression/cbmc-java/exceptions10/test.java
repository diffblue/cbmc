class A extends RuntimeException {}
class B extends A {}
class C extends B {}

public class test {
  static void foo() {
    try {
      A b = new A();
      throw b;
    }
    catch(A exc) {
      assert false;
    }
  }
  
  public static void main (String args[]) {
    try {
      A a = new A();
      foo();
    }
    catch(B exc) {
      assert false;
    }
  }
}
