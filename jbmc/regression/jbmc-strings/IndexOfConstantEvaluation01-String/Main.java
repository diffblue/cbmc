public class Main {

  public void constantIndexOf() {
    String s1 = "abcabc";
    String s2 = "bc";
    assert s1.indexOf(s2) == 1;
    assert s1.indexOf(s2, -10) == 1;
    assert s1.indexOf("") == 0;
    assert s1.indexOf(s2, 3) == 4;
    assert s1.indexOf("cd") == -1;
    assert s1.indexOf(s2, 10) == -1;
    assert s1.indexOf("", 10) == -1;
  }
}
