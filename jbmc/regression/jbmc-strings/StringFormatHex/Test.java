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

  public static void testHexLengthConstPASS() {
    String u = String.format("di%xlue", 255);
    assert u.length() == 7;
  }

  public static void testHexLengthConstFAIL() {
    String u = String.format("di%xlue", 255);
    assert u.length() != 7;
  }
}
