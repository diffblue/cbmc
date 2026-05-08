public class Test implements OtherInterface {

  public static int staticMethod(int x) { return x + 1; }

  private int field = 1;

  public int instanceMethod(int x) { return field + x; }

  // Implement OtherInterface
  public int f(int x) { return x + 1; }

  interface MakeTest {
    public Test makeTest();
  }

  public static void main() {

    IntToInt staticMethodBound = Test::staticMethod;
    Test instance = new Test();
    IntToInt instanceMethodBound = instance::instanceMethod;
    IntToInt interfaceMethodBound = ((OtherInterface)instance)::f;
    MakeTest makeTest = Test::new;

    assert staticMethodBound.f(1) == 2;
    assert interfaceMethodBound.f(1) == 2;
    assert instanceMethodBound.f(1) == 2;
    assert makeTest.makeTest().instanceMethod(1) == 2;

  }
}
