public class Test {

  public static void main() {

    InterfaceWithDefaults interfaceWithDefaults = (x -> x + 1);
    assert interfaceWithDefaults.f(1) == 2;

  }
}
