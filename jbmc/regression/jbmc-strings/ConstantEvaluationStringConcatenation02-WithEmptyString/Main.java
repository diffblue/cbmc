public class Main {
  public void test1() {
    String s1 = "abc";
    String s2 = "";
    String s3 = s1 + s2;
    assert s3.length() == 3;
    assert s3.startsWith("abc");
  }

  public void test2() {
    String s1 = "";
    String s2 = "abc";
    String s3 = s1 + s2;
    assert s3.length() == 3;
    assert s3.startsWith("abc");
  }

  public void test3() {
    String s1 = "";
    String s2 = "";
    String s3 = s1 + s2;
    assert s3.length() == 0;
    assert s3.startsWith("");
  }
}
