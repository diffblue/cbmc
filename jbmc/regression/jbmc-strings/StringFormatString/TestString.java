public class Test {
  public static String string1(String s) {
    if (s == null)
      return "null!";
    String u = String.format("Hello %s !", s);
    if (u.equals("Hello world !"))
      assert(false);
    else if (u.startsWith("impossible!"))
      assert(false);
    else
      assert(false);
    return u;
  }

  public static void string1Length(String s) {
    if (s == null)
      return;
    String u = String.format("Hello %s !", s);
    assert u.length() == 10;
    return 1;
  }

  public static void string1LengthConst() {
    String u = String.format("Hello %s !", "world");
    assert u.length() == 13;
    return 1;
  }
}
