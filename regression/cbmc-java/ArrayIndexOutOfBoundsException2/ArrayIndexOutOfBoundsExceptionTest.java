public class ArrayIndexOutOfBoundsExceptionTest {
  public static void main(String args[]) {
      try {
          int[] a=new int[4];
          int i=a[5];
      }
      catch (ArrayIndexOutOfBoundsException exc) {
          assert false;
      }
  }
}
