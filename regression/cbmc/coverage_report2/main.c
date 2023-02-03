int factorial(int n)
{
  if(n == 0)
  {
    return 1;
  }
  return n * factorial(n - 1);
}

int main(void)
{
  int result = factorial(5);
  return 0;
}
