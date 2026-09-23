int x;

int main()
{
  x = -1;

  for(; x != 100; x++)
    // clang-format off
    __CPROVER_loop_invariant(x>=0 && x<=100) // fails base case
  {
    __CPROVER_assert(x < 100, "non-inductive invariant");
  }
  // clang-format on

  return 0;
}
