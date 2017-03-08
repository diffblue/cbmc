public class jarfile3
{
  public class A
  {
    int x=1;
  }
  public class B
  {
    int x=1;
  }

  void f(int i)
  {
    A a=new A();
    B b=new B();
    assert(a.x==1);
    assert(b.x==1);
  }
}
