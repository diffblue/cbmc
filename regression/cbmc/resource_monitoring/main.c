int factorial(int n)
{
  if(n <= 1)
    return 1;
  return n * factorial(n - 1);
}

int main()
{
  int x;
  __CPROVER_assume(x >= 1 && x <= 5);
  int result = factorial(x);
  __CPROVER_assert(result >= 1, "positive");
}
