public class Test {
  public static String percent() {
    String u = String.format("%s %% %s", "foo", "bar");
    if (u.equals("foo % bar"))
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String percentLength() {
    String u = String.format("%s %% %s", "foo", "bar");
    if (u.length() == 9)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String newline() {
    String u = String.format("%s %n %s", "foo", "bar");
    if (u.equals("foo \n bar"))
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

  public static String newlineLength() {
    String u = String.format("%s %% %s", "foo", "bar");
    if (u.length() == 9)
      assert(false);
    else
      assert(false); // unreachable
    return u;
  }

}
