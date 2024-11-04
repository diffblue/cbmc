int main()
{
  int *r;
  int *a;
#if 1
  _Bool tmp_if_expr;
  if(r == 0)
  {
    tmp_if_expr = 0;
  }
  else
  {
    r = __CPROVER_allocate(sizeof(int), 0);
    tmp_if_expr = 1;
  }

  __CPROVER_assume(tmp_if_expr);
#else
  // this works, because we constant-propagate r as an address-of expression
  __CPROVER_assume(r != 0);
  r = __CPROVER_allocate(sizeof(int), 0);
#endif
  __CPROVER_assume(r != 0);
  __CPROVER_assume(r == a);
  __CPROVER_assert(r == a, " r == a before");
  __CPROVER_assert(*r == *a, "*r == *a before");
}
