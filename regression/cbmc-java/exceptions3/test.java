class A extends Throwable {}
class B extends A {}
class C extends B {}

public class test {
  public static void main (String args[]) {
    try {
      throw new B();
    }
    catch(C exc) {
      assert false;
    }
    catch(B exc) {
      assert false;
    }
  }
}
