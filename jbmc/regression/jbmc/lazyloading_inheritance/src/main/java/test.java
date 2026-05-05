class Base
{
  void f() { }
}

class Middle extends Base
{
}

class Derived extends Middle
{
  void f() { super.f(); }
}


public class test {

  public static void test(Middle foo) {
    if(foo != null ) {
      foo.f();
    }
  }

}
