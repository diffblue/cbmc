public class Main {
  public void test() {
    StringBuilder sb = new StringBuilder("abc");
    sb.append("xyz");
    String s = sb.toString();
    assert s.length() == 6;
    assert s.startsWith("abcxyz");
  }
}
