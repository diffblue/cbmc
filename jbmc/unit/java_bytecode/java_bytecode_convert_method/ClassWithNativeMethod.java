public class ClassWithNativeMethod {
  native boolean f();
  boolean f(int i) {
    return false;
  }
}
