class Z 
{
  public int toInt()
  {
    return 12345;
  }
}

class A extends Z
{
}

class B extends A
{
}

class test
{
  void check()
  {
    B b=new B();
    assert(b.toInt()==12345);
  }
}
