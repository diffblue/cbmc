class A
{
  public void f(){}
};

class B extends A
{
  public void f()
  {
    assert false;
  }
};

class virtual1
{
  public static void main(String[] args)
  {
    A a=new A();
    B b=new B();
    a.f();
  }
}

