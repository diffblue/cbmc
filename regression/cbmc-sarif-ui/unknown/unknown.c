int main()
{
  unsigned x;
  // Always true (2*x is even, so it is never 1) but not constant-folded, so it
  // can never be falsified. Under --stop-on-fail it is therefore left
  // undecided (UNKNOWN), which maps to a SARIF open/warning result.
  __CPROVER_assert(2u * x != 1u, "undecided under stop-on-fail");
  __CPROVER_assert(x == 0u, "fails");
}
