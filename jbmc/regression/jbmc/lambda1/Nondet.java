public class Nondet {
  int x;
  int y;
  public static void test(Nondet nondet) {
    Function<Integer, Integer> lambda = (z) -> nondet.x + nondet.y + z;
    assert(lambda.apply(0) == 42);
  }
}
