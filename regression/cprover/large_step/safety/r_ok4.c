int main()
{
  int *p;
  __CPROVER_assume(__CPROVER_r_ok(p));
  __CPROVER_assert(p != 0, "p is not null");

  return 0;
}
