class A
{
  protected int toInt()
  {
    return 12345;
  }
}

class B extends A
{
  public void secondary()
  {
    assert(toInt()==12345);
  }
}

class test
{
  void check()
  {
    B b=new B();
    b.secondary();
  }
}
