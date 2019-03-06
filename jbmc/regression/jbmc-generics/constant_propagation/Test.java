public class Test {
  public static void main() {
    Generic<Integer> g = new GenericSub<Integer>();

    int x = 0;
    for(int i = 0; i < 1000; ++i)
      x += g.get();

    assert x == 0;
  }
}

class Generic<T> {
  T key;
  int x;

  public int get() { return 0; }

  public Generic() {
    key = null;
    x = 5;
  }
}

class GenericSub<S> extends Generic<S> {
  public int get() { return x; }
}
