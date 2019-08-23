public class Test {
  public void test1() {
    char c = '\uFFFF';
    String s = String.valueOf(c);
    assert s.equals("\uFFFF");
  }

  public void test2() {
    char c = '\uFFFE';
    String s = String.valueOf(c);
    assert s.equals("\uFFFE");
  }
}
