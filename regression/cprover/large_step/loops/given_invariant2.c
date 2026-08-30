int x;

int main()
{
  for(x = 0; x != 100; x++)
    // clang-format off
    __CPROVER_loop_invariant(x>=0 && x<=10) // this is wrong
  {
    __CPROVER_assert(x != 1000, "non-inductive invariant");
  }
  // clang-format on

  return 0;
}
