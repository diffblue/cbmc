public class Test {

  public static void main() {

    ChildInterface inheritedInterface = x -> x + 1;
    assert inheritedInterface.f(1) == 2;

  }
}
