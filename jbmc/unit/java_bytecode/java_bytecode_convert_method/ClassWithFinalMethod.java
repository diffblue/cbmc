public class ClassWithFinalMethod {
  public final int finalFunc() {
    return 0;
  }
  public int nonFinalFunc() {
    return 0;
  }
  public int opaqueFunc() {
    return OpaqueClass.staticFunc();
  }
}
