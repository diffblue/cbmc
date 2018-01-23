class Test {

  public int y = 5;

  public int foo(int x) {
    if (x > 10 && y > 5) {
      return y;
    } else {
      return y * 10;
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
