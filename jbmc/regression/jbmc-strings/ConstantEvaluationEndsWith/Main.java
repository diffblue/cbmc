public class Main {
  public void constantEndsWithPass() {
    String s1 = "abc";
    String s2 = "bc";
    assert s1.endsWith(s2);
  }

  public void constantEndsWithFail() {
    String s1 = "abc";
    String s2 = "d";
    assert s1.endsWith(s2);
  }
}
