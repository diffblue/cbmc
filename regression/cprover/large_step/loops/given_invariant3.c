int x;

int main()
{
  for(x = 0; x < 100; x++)
    // clang-format off
    __CPROVER_loop_invariant(x>=0 && x<=100) // should pass
  {
    // whatnot
  }
  // clang-format on

  __CPROVER_assert(x == 100, "non-inductive property"); // should pass

  return 0;
}
