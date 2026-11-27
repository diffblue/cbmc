void main()
{
  unsigned i = 0, t;
  unsigned *p;
  while(i < 10)
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(i <= 10)
    // clang-format on
    {
      t = i;
      p = &t;
      __CPROVER_assert(*p == i, "*p == i");
      i++;
    }
}
