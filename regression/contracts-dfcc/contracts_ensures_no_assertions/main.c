int f(int x) __CPROVER_requires(x >= 0 && x < 100)
  __CPROVER_ensures(__CPROVER_return_value == x + 2)
{
  return x + 1;
}

int main()
{
  int x;
  __CPROVER_assume(x >= 0 && x < 100);
  return f(x);
}
