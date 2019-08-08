public class Main {
  public void test() {
    StringBuilder sb = new StringBuilder();
    String s = sb.toString();
    assert s.isEmpty();
    assert s.length() == 0;
  }
}
