public class test
{
  public static void check(int i, boolean b) {
    String s = "";

    if (b) {
      s = String.valueOf(123.456);
    }

    if (i == 1)
      assert (!b || s.equals("123.456"));
    else
      assert (!b || !s.equals("123.456"));
  }
}
