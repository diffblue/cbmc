public class Test {

  // In each of these cases a guard is repeated -- either an explicit assertion,
  // or a guard implied by Java's semantics, e.g. that an array index is in bounds.
  // It should be possible to violate the condition the first time, but not the second,
  // as the program would have aborted (without --java-throw-runtime-exceptions) or a
  // runtime exception thrown (with --java-throw-runtime-exceptions).

  public static void testAssertion(boolean condition) {
    assert(condition);
    assert(condition);
  }

  public static void testArrayBounds(int[] array, int index) {
    if(array == null)
      return;
    int got = array[index];
    got = array[index];
  }

  public static void testClassCast(boolean unknown) {
    A maybe_b = unknown ? new A() : new B();
    B definitely_b = (B)maybe_b;
    definitely_b = (B)maybe_b;
  }

  public static void testNullDeref(A maybeNull) {
    int got = maybeNull.field;
    got = maybeNull.field;
  }

  public static void testDivByZero(int unknown) {
    int div = 1 / unknown;
    div = 1 / unknown;
  }

  public static void testArrayCreation(int maybeNegative) {
    int[] arr = new int[maybeNegative];
    arr = new int[maybeNegative];
  }

}

class A { public int field; }
class B extends A {}
