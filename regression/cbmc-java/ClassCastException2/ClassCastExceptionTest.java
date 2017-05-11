class A {}

class B extends A {}

class C extends B {}

public class ClassCastExceptionTest {
  public static void main(String args[]) {
      try {
          A c = new C();
          B b = (B)c;
          // TODO: an explicit throw is currently needed in order
          // for CBMC to convert the exception handler
          throw new RuntimeException();
      }
      catch (ClassCastException exc) {
          assert false;
      }
    
  }
}
