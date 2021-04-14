struct test
{
  int x;
};

void main()
{
  struct test t;
  t.x = 0;

  unsigned n;
  for(unsigned i = 0; i < n; ++i)
    __CPROVER_loop_invariant(i <= n)
    {
      t.x += 2;
    }

  assert(t.x == 0 || t.x == 2);
}
