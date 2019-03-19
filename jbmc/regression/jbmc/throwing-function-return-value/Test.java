public class Test {

  public static Test f(boolean unknown) throws Exception {

    if(unknown)
      throw new Exception();
    else
      return new Test();

  }

  public static void main(boolean unknown) {

    Sub s = new Sub(); // Make sure Sub is loaded
    int x = 0;

    // The routine below is repeated twice because historically symex could
    // behave differently the first and second times a may-throw function was
    // called.

    try {
      Test t1 = f(unknown);
      t1.f();
      x += t1.g();
    }
    catch(Exception e) { }

    try {
      Test t2 = f(unknown);
      t2.f();
      x += t2.g();
    }
    catch(Exception e) { }

    assert x == 10;

  }

  public void f() { }
  public int g() { return 5; }

}

class Sub extends Test {

  public void f() { }
  public int g() { return 0; }

}
