public class NegativeArraySizeExceptionTest {
  public static void main(String args[]) {
      try {
          int a[]=new int[-1];
          throw new RuntimeException();
      }
      catch (NegativeArraySizeException exc) {
          assert false;
      }
  }
}
