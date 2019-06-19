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
    String u = String.format("di%xblue", 255);
    assert u.length() == 8;
  }

  public static void testHexLengthConstFAIL() {
    String u = String.format("di%xblue", 255);
    assert u.length() != 8;
  }

  public static String testHexEval() {
    String u = String.format("di%xblue", 255);
    assert false;
    return u;
  }

  public static String testHexEvalUpper() {
    String u = String.format("di%Xblue", 255);
    assert false;
    return u;
  }
}
