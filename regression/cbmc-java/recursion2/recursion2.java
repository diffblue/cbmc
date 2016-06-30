class recursion2
{
  public static void main(String[] args)
  {
    assert recursion_test(0)==10;
  }
  
  static int recursion_test(int depth)
  {
    if(depth<10)
      return recursion_test(depth+1)+1;
    else
      return 0;
  }
}
