public class recursion1
{
  static int f(int n)
  {
    if(n <= 0)
      return 1;
    else
      return n * f(n-1);
  }

  public static void main(String[] args)
  {
    assert f(1)==1;
  }
}
