public class Main {

  public void constantIndexOf(String s, char c, int i) {

    String s1 = "abcabc";
    String s2 = "bc";

    assert s1.indexOf(c) == 1;
    assert s1.indexOf(s) == 1;
    assert s1.indexOf(c, 1) == 1;
    assert s1.indexOf(s, 1) == 1;

    assert s.indexOf('a') == 1;
    assert s.indexOf(s1) == 1;
    assert s.indexOf('a', 1) == 1;
    assert s.indexOf(s1, 1) == 1;

    assert s1.indexOf(s, -10) == 1;
    assert s1.indexOf(c, -10) == 1;

    assert s1.indexOf(s2, i) == 1;
    assert s1.indexOf('a', i) == 1;
  }
}
