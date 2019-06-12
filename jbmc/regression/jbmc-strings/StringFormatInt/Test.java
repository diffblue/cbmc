public class Test {
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

  public static void testIntLength(int i) {
    String u = String.format("Hello %d !", i);
    assert u.length() == 20;
  }

  public static void testIntLengthConstPASS() {
    String u = String.format("Hello %d !", -12345);
    assert u.length() == 14;
  }

  public static void testIntLengthConstFAIL() {
    String u = String.format("Hello %d !", -12345);
    assert u.length() != 14;
  }
}
