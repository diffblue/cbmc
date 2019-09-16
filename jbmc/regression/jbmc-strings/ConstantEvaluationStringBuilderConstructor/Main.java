public class Main {
  public void testSuccess1() {
    StringBuilder sb = new StringBuilder();
    assert sb.toString().equals("");
  }

  public void testSuccess2() {
    StringBuilder sb = new StringBuilder(0);
    assert sb.toString().equals("");
    sb = new StringBuilder(5);
    assert sb.toString().equals("");
  }

  public void testSuccess3(int i) {
    // The capacity argument of StringBuilder is ignored by the constant
    // propagator, hence we can still constant propagate the two constructors
    StringBuilder sb = new StringBuilder(i);
    assert sb.toString().equals("");
    sb = new StringBuilder(i);
    assert sb.toString().equals("");
  }

  public void testSuccess4() {
    StringBuilder sb = new StringBuilder("abc");
    assert sb.toString().equals("abc");
  }

  public void testSuccess5() {
    CharSequence cs = "abc";
    StringBuilder sb = new StringBuilder(cs);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation1(String s) {
    StringBuilder sb = new StringBuilder(s);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation2(CharSequence cs) {
    StringBuilder sb = new StringBuilder(cs);
    assert sb.toString().equals("abc");
  }
}
