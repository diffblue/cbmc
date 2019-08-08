public class Nondet {
  int x;
  int y;
  public static void test(Nondet nondet) {
    Function<Integer, Integer> lambda = (z) -> nondet.x + nondet.y + z;
    assert (lambda.apply(0) == 42);
  }
  public static void testPrimitiveArray(int[] ints) {
    Function<Integer, Integer> lambda = (index) -> ints[index];
    assert (lambda.apply(0) == 42);
  }
  public static void testReferenceArray(Nondet[] nondets) {
    Function<Integer, Integer> lambda = (index) -> nondets[index].x;
    assert (lambda.apply(0) == 42);
  }
}
