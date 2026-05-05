import org.cprover.MyClass;
import org.cprover.other.MyOther;

public class Main {
  public static void main(String[] args) {
    int x = 42;
    int y = myMethod(x);
    MyClass m = new MyClass(y);
    int z = m.get();
    int w = MyClass.Inner.doIt(z);
    int u = MyOther.identity(w);
    assert(x == y);
    assert(y == z);
    assert(z == w);
    assert (w == u);
  }

  public static int myMethod(int x) {
    return x;
  }
}
