int main(void)
{
  int *p;
  __CPROVER_assume(__CPROVER_rw_ok(p));

  int i;
  __CPROVER_assert(__CPROVER_rw_ok(p), "property 1"); // should pass

  p = &i; // take address of i

  return 0;
}
