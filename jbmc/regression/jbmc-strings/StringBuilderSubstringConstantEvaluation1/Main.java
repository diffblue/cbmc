public class Main {
  public void test() {
    StringBuilder sb = new StringBuilder("abc");

    String s1 = sb.substring(0);
    assert s1.length() == 3;
    assert s1.startsWith("abc");

    String s2 = sb.substring(1);
    assert s2.length() == 2;
    assert s2.startsWith("bc");

    String s3 = sb.substring(0, 3);
    assert s3.length() == 3;
    assert s3.startsWith("abc");

    String s4 = sb.substring(0, 0);
    assert s4.length() == 0;
    assert s4.startsWith("");

    String s5 = sb.substring(0, 1);
    assert s5.length() == 1;
    assert s5.startsWith("a");
  }
}
