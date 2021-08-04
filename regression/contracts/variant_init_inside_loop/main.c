int main()
{
  unsigned start, max;
  unsigned i = start;

  while(i < max)
    // clang-format off
    __CPROVER_loop_invariant(
      (start > max && i == start) ||
      (start <= i && i <= max)
    )
    __CPROVER_decreases(max - i)
    // clang-format on
    {
      i++;
    }

  return 0;
}
