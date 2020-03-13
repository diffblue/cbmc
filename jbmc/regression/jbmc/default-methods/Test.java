public class Test extends Parent implements TestInterface, BothInterface {

  public int parentInterfaceOverriddenByTest(int x) { return x + 7; }
  public int testInterfaceOverriddenByTest(int x) { return x + 8; }

  public static void testme() {

    Test test = new Test();
    assert test.testInterfaceNotOverridden(1) == 2;
    assert test.testInterfaceOverriddenByTest(1) == 9;
    assert test.parentInterfaceNotOverridden(1) == 4;
    assert test.parentInterfaceOverriddenByParent(1) == 7;
    assert test.parentInterfaceOverriddenByTest(1) == 8;
    assert test.testInterfaceOverriddenByParent(1) == 11;
    assert test.bothInterfaceOverriddenByParent(1) == 13;

    // Check we made it here:
    assert false;

  }

  public static void main(String[] args) { testme(); }

}

class Parent implements ParentInterface, BothInterface {

  public int parentInterfaceOverriddenByParent(int x) { return x + 6; }
  // Note this isn't an override here, as this class doesn't implement TestInterface,
  // but it will become one when Test implements that interface.
  public int testInterfaceOverriddenByParent(int x) { return x + 10; }
  public int bothInterfaceOverriddenByParent(int x) { return x + 12; }

}

interface TestInterface {

  default int testInterfaceNotOverridden(int x) { return x + 1; }
  default int testInterfaceOverriddenByTest(int x) { return x + 2; }
  default int testInterfaceOverriddenByParent(int x) { return x + 9; }

}

interface ParentInterface {

  default int parentInterfaceNotOverridden(int x) { return x + 3; }
  default int parentInterfaceOverriddenByParent(int x) { return x + 4; }
  default int parentInterfaceOverriddenByTest(int x) { return x + 5; }

}

interface BothInterface {

  default int bothInterfaceOverriddenByParent(int x) { return x + 11; }

}
