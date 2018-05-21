public class Test {

  private int foo(int x) {
    if (x > 10) {
      return x;
    } else {
      return x * 10;
    }
  }

  protected int bar(int x) {
    if (x < 10) {
      return x;
    } else {
      return x / 10;
    }
  }
}
