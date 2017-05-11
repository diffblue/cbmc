public class ClassCastExceptionTest {
  public static void main(String args[]) {
      try {
          Object x = new Integer(0);
          String y = (String)x;
          throw new RuntimeException();
      }
      catch (ClassCastException exc) {
          assert false;
      }
    
  }
}
