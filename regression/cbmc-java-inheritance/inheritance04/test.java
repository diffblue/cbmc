class A
{
  public int toInt()
  {
    return 12345;
  }
}

class B extends A
{
  public int toInt()
  {
    return 9999;
  }
}

class Z extends B
{
}

class test
{
  void check()
  {
    Z z=new Z();
    assert(z.toInt()==9999);
  }
}
