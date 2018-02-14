public class Test extends Parent implements InterfaceWithStatic {

  public static void main() {

    int val1 = InterfaceWithStatic.x;
    int val2 = x;
    assert val1 == val2;

  }

}

class Parent {

}

