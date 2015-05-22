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

class virtual2
{
  public static void main(String[] args)
  {
    A a=new B();
    a.f();
  }
}

