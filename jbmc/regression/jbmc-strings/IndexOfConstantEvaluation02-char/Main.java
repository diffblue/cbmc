public class Main {

  public void constantIndexOf() {
    String s1 = "abcabc";
    assert s1.indexOf('b') == 1;
    assert s1.indexOf('b', -10) == 1;
    assert s1.indexOf('b', 3) == 4;
    assert s1.indexOf('d') == -1;
    assert s1.indexOf('b', 10) == -1;
  }
}
