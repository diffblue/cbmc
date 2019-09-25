public class Thrower {
  public static void test(Integer t) {
    String ret = "";
    if (t != null)
      try {
        switch (t) {
        case 1:
          ret = "CCE";
          Object o = new Integer(0);
          String x = ((String) o);
          break;

        case 2:
          ret = "AIOBE";
          int[] xs = new int[3];
          t = xs[5];

        case 3:
          ret = "AE";
          t = 5 / 0;

        case 4:
          ret = "NASE";
          Integer[] arr = new Integer[-7];

        case 5:
          ret = "NPE";
          String str = null;
          str.toLowerCase();
          
        default:
          break;
        }
      } catch (ClassCastException | NegativeArraySizeException
               | NullPointerException | ArithmeticException
               | ArrayIndexOutOfBoundsException e3) {

        if (e3 instanceof ClassCastException)
          assert ret.equals("CCE");

        if (e3 instanceof NegativeArraySizeException)        
          assert ret.equals("NASE");

        if (e3 instanceof NullPointerException)
          assert ret.equals("NPE");
       
        if (e3 instanceof ArithmeticException)
          assert ret.equals("AE");

        if (e3 instanceof ArrayIndexOutOfBoundsException)
          assert ret.equals("AIOBE");
      }
  }
}
