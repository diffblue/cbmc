public class Main {
  public void testSuccess1() {
    String s = new String();
    assert s.equals("");
  }

  public void testSuccess2() {
    String s = new String("abc");
    assert s.equals("abc");
  }

  public void testSuccess3() {
    StringBuilder sb = new StringBuilder("abc");
    String s = new String(sb);
    assert s.equals("abc");
  }

  public void testSuccess4() {
    StringBuffer sb = new StringBuffer("abc");
    String s = new String(sb);
    assert s.equals("abc");
  }

  public void testNoPropagation1(String s1) {
    String s2 = new String(s1);
    assert s2.equals("abc");
  }

  public void testNoPropagation2(StringBuilder sb) {
    String s = new String(sb);
    assert s.equals("abc");
  }

  public void testNoPropagation3(StringBuffer sb) {
    String s = new String(sb);
    assert s.equals("abc");
  }
}
