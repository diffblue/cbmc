public class Main {
  public void test() {
    String s1 = "abc";
    String s2 = "xyz";
    String s3 = s1 + s2;
    assert s3.length() == 6;
    assert s3.startsWith("abcxyz");
  }
}
