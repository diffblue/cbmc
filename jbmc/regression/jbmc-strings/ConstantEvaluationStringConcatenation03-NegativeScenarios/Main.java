public class Main {
  public void test1(String s1) {
    String s2 = "abc";
    assert (s1 + s2).startsWith("abc");
  }

  public void test2(String s) { assert ("" + s).startsWith("abc"); }

  public void test3(String s) { assert (s + s).startsWith("abc"); }
}
