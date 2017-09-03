class A {}

class B extends A {}

class C extends B {}

public class ClassCastExceptionTest {
  public static void main(String args[]) {
      try {
          A c = new C();
          B b = (B)c;
      }
      catch (ClassCastException exc) {
          assert false;
      }
    
  }
}
