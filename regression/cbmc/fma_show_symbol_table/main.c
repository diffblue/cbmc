double f(double x)
{
  return __CPROVER_fma(x, x, 1.0);
}

int main()
{
  double r = f(2.0);
  __CPROVER_assert(r == 5.0, "fma");
  return 0;
}
