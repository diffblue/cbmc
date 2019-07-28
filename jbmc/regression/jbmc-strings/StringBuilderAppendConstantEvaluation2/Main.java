public class Main {
  public void test1() {
    StringBuilder sb1 = new StringBuilder("abc");
    String s2 = "";
    sb1.append(s2);
    assert sb1.length() == 3;
    assert sb1.toString().startsWith("abc");
  }

  public void test2() {
    StringBuilder sb1 = new StringBuilder();
    String s2 = "abc";
    sb1.append(s2);
    assert sb1.length() == 3;
    assert sb1.toString().startsWith("abc");
  }

  public void test3() {
    StringBuilder sb1 = new StringBuilder();
    String s2 = "";
    sb1.append(s2);
    assert sb1.length() == 0;
    assert sb1.toString().startsWith("");
  }
}
