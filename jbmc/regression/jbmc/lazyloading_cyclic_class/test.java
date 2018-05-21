class cycle1
{
  Middle c;
}

class Base
{
  void f() { }
}

class Middle extends Base
{
  cycle1 c;
}

class Derived extends Middle
{
  void f() { }
}

class Foo
{
  public cycle1 entry;
}

public class test {

  public static void test(Foo foo) {
    if(foo != null && foo.entry != null && foo.entry.c != null) {
      foo.entry.c.f();
    }

  }
}
