class Base
{
  void f() { }
}

class Middle extends Base
{
}

class Derived extends Middle
{
  void f() { }
}

class Foo
{
  public Middle m;
}

public class test {

  public static void test(Foo foo) {
    if(foo != null && foo.m != null) {
      foo.m.f();
    }
  }
}
