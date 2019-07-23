public class Main {
  public void test() {
    String s = "abc";

    String s1 = s.substring(0);
    assert s1.equals("abc");

    String s2 = s.substring(1);
    assert s2.equals("bc");

    String s3 = s.substring(0, 3);
    assert s3.equals("abc");

    String s4 = s.substring(0, 0);
    assert s4.equals("");

    String s5 = s.substring(0, 1);
    assert s5.equals("a");
  }
}
