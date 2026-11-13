public class Test {
  public static void check(int x) {
    assert x != 7;
    // Only reachable if the first assertion holds
    assert x != 7;
  }
}
