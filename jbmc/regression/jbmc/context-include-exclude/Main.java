import org.cprover.MyClass;

public class Main {
  public static void main(String[] args) {
    int x = 42;
    int y = myMethod(x);
    MyClass m = new MyClass(y);
    int z = m.get();
    int w = MyClass.Inner.doIt(z);
    assert(x == y);
    assert(y == z);
    assert(z == w);
  }

  public static int myMethod(int x) {
    return x;
  }
}
