package foo;

public class Test {
  public int foo(int x) {
    if (x > 10) {
      return x;
    } else {
      int y = x * 10;
      return y;
    }
  }

  public int bar(int x) {
    if (x < 10) {
      return x;
    } else {
      return x / 10;
    }
  }
}
