public class Main {
  public void constantIsEmptyPass() {
    String s = "";
    assert s.isEmpty();
  }

  public void constantIsEmptyFail() {
    String s = "abc";
    assert s.isEmpty();
  }
}
