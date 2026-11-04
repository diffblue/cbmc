public class Test {
  static class A {}

  static class B {}

  public static void main() {
    Class<?> a = A.class;
    Class<?> b = B.class;
    assert a != b;
    // at least the class literals of A and B have been initialised
    assert org.cprover.regression.ClassLiteralCounter.count[0] >= 2;
  }
}
