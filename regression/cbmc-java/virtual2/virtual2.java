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
    A a=new A();
    A b=new B();
    b.f();
  }
}

