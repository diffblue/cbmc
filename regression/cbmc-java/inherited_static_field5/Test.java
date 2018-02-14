public class Test extends OpaqueParent implements InterfaceWithStatic {

  public static void main() {

    int val1 = x;
    int val2 = InterfaceWithStatic.x;
    assert val1 == val2;

  }

}

class OpaqueParent {

}

