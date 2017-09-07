public class static_init {

  // A should be initialised first, then B will begin init
  // after A.x is set.
  public static void main() {
    assert(A.x == 1 && B.x == 1 && B.y == 2 && A.y == 2);
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
