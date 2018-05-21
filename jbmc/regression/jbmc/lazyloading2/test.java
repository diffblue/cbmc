// This test checks that because A is instantiated in main and B is not,
// A::f is reachable and B::g is not

public class test
{
  A a;
  B b;
  public static void main()
  {
    A a = new A();
    a.f();
  }
}

class A
{
  public void f() {}
}

class B
{
  public void g() {}
}
