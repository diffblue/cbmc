public class Main {
  public void test1() {
    String s1 = "abc";
    String s2 = "xyz";
    String s3 = s1 + s2;
    assert s3.length() == 7;
  }

  public void test2() {
    String s1 = "abc";
    String s2 = "xyz";
    String s3 = s1 + s2;
    assert s3.startsWith("abcdefg");
  }
}
