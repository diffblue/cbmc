public class Main {
  public void test1() {
    StringBuffer sb1 = new StringBuffer("abc");
    String s2 = "";
    sb1.append(s2);
    assert sb1.toString().equals("abc");
  }

  public void test2() {
    StringBuffer sb1 = new StringBuffer();
    String s2 = "abc";
    sb1.append(s2);
    assert sb1.toString().equals("abc");
  }

  public void test3() {
    StringBuffer sb1 = new StringBuffer();
    String s2 = "";
    sb1.append(s2);
    assert sb1.toString().equals("");
  }
}
