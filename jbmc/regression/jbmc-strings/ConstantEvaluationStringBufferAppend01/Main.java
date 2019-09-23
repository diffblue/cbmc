public class Main {
  public void test() {
    StringBuffer sb = new StringBuffer("abc");
    sb.append("xyz");
    assert sb.toString().equals("abcxyz");
  }
}
