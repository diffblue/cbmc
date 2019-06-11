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
}
