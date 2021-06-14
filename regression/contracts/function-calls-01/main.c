int f1(int *x1)
  // clang-format off
  __CPROVER_requires(*x1 > 1)
  __CPROVER_requires(*x1 < 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x1 + 1)
// clang-format on
{
  return *x1 + 1;
}

int main()
{
  int p;
  __CPROVER_assume(p > 1 && p < 10000);
  f1(&p);

  return 0;
}
