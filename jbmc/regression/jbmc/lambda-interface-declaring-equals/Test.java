public class Test {

  public static void main() {

    InterfaceDeclaringEquals interfaceDeclaringEquals = (x -> x + 1);
    int result = interfaceDeclaringEquals.f(1);
    assert result == 2;

  }
}
