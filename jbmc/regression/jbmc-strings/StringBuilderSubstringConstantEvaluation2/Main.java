public class Main {
  public void test1(StringBuilder sb) {
    String s = sb.substring(0);
    assert s.startsWith("xyz");
  }

  public void test2(int i) {
    StringBuilder sb = new StringBuilder("abc");

    String s = sb.substring(i);
    assert s.startsWith("xyz");
  }

  public void test3(StringBuilder sb, int i) {
    String s = sb.substring(i);
    assert s.startsWith("xyz");
  }
}
