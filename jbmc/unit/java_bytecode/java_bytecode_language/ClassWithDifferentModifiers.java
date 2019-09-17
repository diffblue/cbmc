public class ClassWithDifferentModifiers {

  public static void main(String[] args) {
    ClassWithDifferentModifiers guineaPig = new ClassWithDifferentModifiers();
    assert guineaPig.testPublicInstance() == 1;
    assert guineaPig.testPrivateStatic() == 2;
    assert guineaPig.testProtectedFinalInstance() == 3;
    assert guineaPig.testDefaultFinalStatic() == 4;
  }

  public int testPublicInstance() { return 1; }

  private static int testPrivateStatic() { return 2; }

  protected final int testProtectedFinalInstance() { return 3; }

  final static int testDefaultFinalStatic() { return 4; }
}
