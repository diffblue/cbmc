class A extends RuntimeException {
  int i;
  A() {
    i = 1;
  }
}
class B extends A {}
class C extends B {}

public class test {
  public static void main (String args[]) {
    try {
      try {
	int i = 0;
	throw new A();
      }
      catch(A exc) {
	assert exc.i==2;
      }
    }
    catch(B exc) {
      assert exc.i==2;
    }

  }
}
