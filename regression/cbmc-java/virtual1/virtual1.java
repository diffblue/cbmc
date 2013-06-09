class A
{
  int f()
  {
    return 1;
  }
};

class B extends A
{
  int f()
  {
    return 2;
  }
};

class virtual1
{
  public static void main(String[] args)
  {
    int ret_value;
    A a=new B();
    
    ret_value=a.f();
    assert ret_value==2;
  }
}

