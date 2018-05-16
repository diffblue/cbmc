public class ArrayIndexOutOfBoundsExceptionTest {
  public static void main(String args[]) {
      try {
          int[] a=new int[4];
          a[4]=0;
      }
      catch (ArrayIndexOutOfBoundsException exc) {
          assert false;
      }
  }
}
