public class Test {
  public static String testBool(boolean b) {
    String u = String.format("bool: %b", b);
    if (u.equals("bool: true"))
      assert(false);
    else if (u.equals("bool: false"))
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String testBoolLength(boolean b) {
    String u = String.format("bool: %b", b);
    if (u.length() == 10)
      assert(false);
    else if (u.length() == 11)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String testBoolLengthTrue() {
    String u = String.format("bool: %b", true);
    if (u.length() == 10)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String testBoolLengthFalse() {
    String u = String.format("bool: %b", false);
    if (u.length() == 11)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String testBoolLengthNull() {
    Boolean b = null;
    String u = String.format("bool: %b", b);
    if (u.length() == 11)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }
}
