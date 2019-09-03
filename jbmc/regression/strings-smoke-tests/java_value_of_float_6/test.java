public class test {
  public static void check(int i, boolean b) {
    String s = "";

    if (b) {
      s = String.valueOf(1.25f);
    }

    if (i == 1)
      assert (!b || s.equals("1.25"));
    else
      assert (!b || !s.equals("1.25"));
  }
}
