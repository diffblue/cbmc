class A extends RuntimeException {}
class B extends A {}
class C extends B {}

public class test {
  static void foo (int x) {
    try {
      x++;
    }
    catch(A exc) {
      assert false;
    }

    try {
      throw new B();
    }
    catch(B exc) {
      assert false;
    }
  }
}
