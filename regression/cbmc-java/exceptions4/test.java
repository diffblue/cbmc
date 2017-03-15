class A extends Throwable {}
class B extends A {}
class C extends B {}

public class test {
  public static void main (String args[]) {
    try {
      B b = new B();
      throw b;
    }
    catch(C exc) {
      System.out.println("C");
      assert false;
    }
    catch(B exc) {
      System.out.println("B");
    }
  }
}


