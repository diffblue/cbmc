void main()
{
  unsigned i = 0, t;
  while(i < 10 && (i == 0 || t + 1 == i))
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(i <= 10)
    // clang-format on
    {
      t = i;
      i++;
    }
}
