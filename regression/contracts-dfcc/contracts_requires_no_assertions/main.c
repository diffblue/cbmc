int f(int x) __CPROVER_requires(x >= 0 && x < 100)
  __CPROVER_ensures(__CPROVER_return_value == x + 1)
{
  return x + 1;
}

int main()
{
  int x;
  return f(x);
}
