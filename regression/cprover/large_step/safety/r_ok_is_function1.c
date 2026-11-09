int main()
{
  int *p, *q;

  if(p == q)
    __CPROVER_assert(
      __CPROVER_r_ok(p, 1) == __CPROVER_r_ok(q, 1), "property 1");

  return 0;
}
