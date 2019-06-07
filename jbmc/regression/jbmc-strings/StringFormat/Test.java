public class Test {
  public static String testHex(int i) {
    String u = String.format("di%xlue", i);
    if (u.equals("diffblue"))
      assert(false);
    else if (u.startsWith("di"))
      assert(false);
    else
      assert(false);
    return u;
  }

  public static String testInt(int i) {
    String u = String.format("Hello %d !", i);
    if (u.equals("Hello 10 !"))
      assert(false);
    else if (!u.startsWith("Hello"))
      assert(false);
    else
      assert(false);
    return u;
  }

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

  public static String string2(String s, String t) {
    if (s == null || t == null)
      return "null null";
    String u = String.format("%s %s", s, t);
    assert(!u.equals("ab"));
    return u;
  }

  public static String string3(String s, String t) {
    if (s == null || t == null)
      return "null null";
    String u = String.format("%s%s%s", s, t, s);
    assert(s.length() != 1 || u.charAt(0) == u.charAt(u.length() - 1));
    return u;
  }

  public static String float1(float f) {
    String u = String.format("Pi is %.2f.", 3.14);
    // We are not checking the exactness of the string produced, just that
    // the solver will not crash.
    assert(u.length() > 0);
    assert(u.charAt(0) == 'P');
    return u;
  }

}
