void main()
{
  unsigned i = 0, x;
  while(i < 10)
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(i <= 10)
    // clang-format on
    {
      x = i;
      i++;
    }
  __CPROVER_assert(x == 9, "x == 9");
}
