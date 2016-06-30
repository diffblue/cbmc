public class recursion1
{
  int f(int n)
  {
    if(n <= 0)
      return 1;
    else
      return n * f(n-1);
  }
}
