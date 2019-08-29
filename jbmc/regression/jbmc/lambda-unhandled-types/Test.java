public class Test {

  public static void main() {

    StubInterface stubInterface = (x -> x);
    StubSuperinterface stubSuperinterface = (x -> x);
    InterfaceDeclaringEquals interfaceDeclaringEquals = (x -> x);
    InterfaceWithDefaults interfaceWithDefaults = (x -> x);
    ChildInterface inheritedInterface = x -> x;
  }
}
