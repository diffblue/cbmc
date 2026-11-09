int main()
{
  int *p;
  __CPROVER_assume(__CPROVER_r_ok(p));
  {
    int x;
    __CPROVER_assert(p != &x, "property 1"); // passes
  }
  __CPROVER_assert(__CPROVER_r_ok(p), "property 2"); // passes
}
