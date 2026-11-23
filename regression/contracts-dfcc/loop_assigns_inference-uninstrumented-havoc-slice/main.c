// A function that DFCC does not instrument (through its `__VERIFIER` prefix)
// and havocs what its parameter points to.
void __VERIFIER_havoc(int *p)
{
  __CPROVER_havoc_slice(p, sizeof(int));
}

int main()
{
  int y = 1;

  // The write happens in a later iteration than the first, so that the
  // assertion after the loop only fails if the loop havocs y.
  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      if(i == 5)
        __VERIFIER_havoc(&y);
    }
  __CPROVER_assert(y == 1, "y havocked through a parameter");
  return 0;
}
