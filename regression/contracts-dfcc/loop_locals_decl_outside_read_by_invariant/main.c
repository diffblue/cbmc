void main()
{
  unsigned i = 0, t = 0;
  while(i < 10)
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(i <= 10 && t == 0)
    // clang-format on
    {
      t = i;
      i++;
    }
}
