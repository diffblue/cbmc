public class Main {
  public void test1(String s1) {
    String s2 = s1.substring(0);
    assert s2.startsWith("xyz");
  }

  public void test2(int i) {
    String s1 = "abc";

    String s2 = s1.substring(i);
    assert s2.startsWith("xyz");
  }

  public void test3(String s1, int i) {
    String s2 = s1.substring(i);
    assert s2.startsWith("xyz");
  }
}
