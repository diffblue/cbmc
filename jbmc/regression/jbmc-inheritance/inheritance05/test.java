interface A
{
  public int toInt();
}

class B implements A
{
  public int toInt()
  {
    return 12345;
  }
}

class test
{
  void check()
  {
    B b=new B();
    assert(b.toInt()==12345);
  }
}
