void main()
{
  unsigned i = 0, t, *p = 0;
  while(i < 10)
    // clang-format off
    __CPROVER_assigns(i, p)
    __CPROVER_loop_invariant(i <= 10)
    // clang-format on
    {
      p = &t;
      t = i;
      i++;
    }
  if(p)
    __CPROVER_assert(*p == 9, "*p == 9");
}
