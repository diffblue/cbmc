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
}
