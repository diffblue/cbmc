// The most basic lazy loading test: A::f is directly called, B::g should be unreachable

public class test
{
  A a;
  B b;
  public static void main()
  {
    A.f();
  }
}

class A
{
  public static void f() {}
}

class B
{
  public static void g() {}
}
