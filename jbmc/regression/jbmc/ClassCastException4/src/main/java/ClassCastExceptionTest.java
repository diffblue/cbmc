public class ClassCastExceptionTest {
  public static void main(String args[]) {
    try {
      Object[] x = new Integer[1];
      String[] y = (String[])x;
    } catch (ClassCastException exc) {
      assert false;
    }
  }
}
