// Test that virtual method resolution works through Object parameters
public class SimpleEquals {
  static int counter = 0;

  static class MyClass {
    public String toString() {
      counter++;
      return "MyClass";
    }
  }

  public static void testDirect() {
    MyClass m = new MyClass();
    m.toString();
    assert(counter == 1);
  }

  public static void testThroughObject(Object o) {
    // Virtual call through Object parameter should resolve to MyClass.toString
    o.toString();
    assert(counter == 2);
  }

  public static void main(String[] args) {
    testDirect();
    testThroughObject(new MyClass());
  }
}
