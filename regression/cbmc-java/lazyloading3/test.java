// This test checks that because `main` has a parameter of type C, which has a field of type A,
// A::f is considered reachable, but B::g is not.

public class test
{
  public static void main(C c)
  {
    if(c==null || c.a==null)
      return;
    c.a.f();
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

class C
{
  A a;
}

class D
{
  B b;
}
