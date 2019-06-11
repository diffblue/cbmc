public class TestHex {
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
}
