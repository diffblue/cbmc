void test(int *x, int *y)
{
  __CPROVER_assert(x, "assertion x");
  __CPROVER_assert(y, "assertion y");
  __CPROVER_assert(x == y, "assertion x == y");
  __CPROVER_assert(x != y, "assertion x != y");
  __CPROVER_assert(*x == *y, "assertion *x == *y");
}
