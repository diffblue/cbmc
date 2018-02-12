public class Test implements OpaqueInterfaceWithStatic {

  public static void main() {

    int val1 = x;
    int val2 = OpaqueInterfaceWithStatic.x;
    assert val1 == val2;

  }

}

