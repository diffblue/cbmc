public class Main {
  public void constantCompareToPass() {
    String s1 = "ab";
    String s2 = "abc";
    assert s1.compareTo(s2) == -1;
    assert s2.compareTo(s1) == 1;
    s1 = "abc";
    s2 = "abc";
    assert s1.compareTo(s2) == 0;
    s1 = "abyz";
    s2 = "adyz";
    assert s1.compareTo(s2) == -2;
  }

  public void constantCompareToFail1() {
    String s1 = "ab";
    String s2 = "abc";
    assert s1.compareTo(s2) != -1;
  }

  public void constantCompareToFail2() {
    String s1 = "ab";
    String s2 = "abc";
    assert s2.compareTo(s1) != 1;
  }

  public void constantCompareToFail3() {
    String s1 = "abc";
    String s2 = "abc";
    assert s1.compareTo(s2) != 0;
  }

  public void constantCompareToFail4() {
    String s1 = "abyz";
    String s2 = "adyz";
    assert s1.compareTo(s2) != -2;
  }
}
