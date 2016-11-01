class A {
  int i;
}

class B extends A {
  int j;
}

public class minim {
  public static void f(int x, int y) {
      B b = new B();
      if(x == 0) {
	b.i = 5;
	if(y < 5) {
	  b.j = 1;
	}
      }
    }
}
