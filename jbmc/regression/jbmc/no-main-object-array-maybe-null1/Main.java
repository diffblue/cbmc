public class Main
{
  public static class A {
    int x;
  }
  public A a;

  public static void main(Main[] args)
  {
    assert(args != null); // allowed to fail
    if(args != null && args.length > 0) {
      Main m = args[0];
      if(m != null) {
        assert(m.a == null); // allowed to fail
      }
    }
  }
}
