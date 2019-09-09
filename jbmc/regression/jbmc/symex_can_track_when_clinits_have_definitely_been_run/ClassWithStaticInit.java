public class ClassWithStaticInit {
  public static int x;

  static { x = 42; }

  public static int getStaticValue() { return x; }
}
