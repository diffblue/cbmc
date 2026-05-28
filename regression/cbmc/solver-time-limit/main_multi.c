int main()
{
  int a, b;
  __CPROVER_assume(a >= 0 && a < 10);
  __CPROVER_assume(b >= 0 && b < 10);
  __CPROVER_assert(a + b >= 0, "sum is non-negative");
  __CPROVER_assert(a < 10, "a is bounded");
  __CPROVER_assert(b < 10, "b is bounded");
  return 0;
}
