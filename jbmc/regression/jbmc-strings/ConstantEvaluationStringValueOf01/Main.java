public class Main {
  public void testPropagation() {
    assert String.valueOf(7).equals("7");
    assert String.valueOf(7L).equals("7");
    assert String.valueOf(1.25F).equals("1.25");
    assert String.valueOf(1.25D).equals("1.25");
  }
}
