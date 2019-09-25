public class Test {
  public static void check(Integer t) {
    if (t != null)
      try {
        Integer[] arr = new Integer[-7];
        assert false;
      } catch (NegativeArraySizeException e) {
        assert false;
      }
  }
}
