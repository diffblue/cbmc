class A
{
  public int toInt()
  {
    return 12345;
  }
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
