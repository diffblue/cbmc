void foo(int *p) __CPROVER_requires(__CPROVER_w_ok(p)) __CPROVER_assigns(*p)
{
  int i;

  i = 123;
  *p = 456;                                 // p cannot point to i as i is local
  __CPROVER_assert(i == 123, "property 1"); // should pass
}
