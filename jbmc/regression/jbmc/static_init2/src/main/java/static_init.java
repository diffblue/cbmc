public class static_init {

  // B will begin init first, but then begin A init before it
  // has set B.y, leading to the unintuitive result given here.
  public static void main() {
    assert(B.x == 1 && B.y == 2 && A.x == 1 && A.y == 0);
  }

}

class A {

  public static int x;
  public static int y;
  static {
    x = 1;
    y = B.y;
  }

}

class B {

  public static int x;
  public static int y;
  static {
    x = A.x;
    y = 2;

  }

}
