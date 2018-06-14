class Test
{
  public static void main(String[] args)
  {
    AssertionError a = new AssertionError();
    if(false)
      throw a;
  }
}
