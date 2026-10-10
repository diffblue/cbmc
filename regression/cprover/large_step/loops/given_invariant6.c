int main()
{
  for(int x = 0; x != 100; x++)
    // clang-format off
    __CPROVER_loop_invariant(0) // fails base case
  {
    __CPROVER_assert(0, "property 1");
  }
  // clang-format on

  return 0;
}
