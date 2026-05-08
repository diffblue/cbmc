public class Test {

  public static void main() {

    InterfaceDeclaringHashCode interfaceDeclaringHashCode = (x -> x + 1);
    int result = interfaceDeclaringHashCode.f(1);
    assert result == 2;

  }
}
