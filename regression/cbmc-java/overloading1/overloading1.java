class overloading1
{
  public static void main(String[] args)
  {
    assert(f(1)==1);
    assert(f(1.0d)==2);
  }
  
  static int f(int i)
  {
    return 1;
  }

  static int f(double d)
  {
    return 2;
  }
}

