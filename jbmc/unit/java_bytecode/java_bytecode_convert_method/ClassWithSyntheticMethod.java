public class ClassWithSyntheticMethod {
  private static int inaccessible() {
    return 42;
  }

  public class Inner {
    public int access() {
      return inaccessible();
    }
  }
}
