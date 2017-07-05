public class NegativeArraySizeExceptionTest {
  public static void main(String args[]) {
      try {
          int a[]=new int[-1];
      }
      catch (NegativeArraySizeException exc) {
          assert false;
      }
  }
}
