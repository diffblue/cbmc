int g;

unsigned foo(unsigned n)
  // clang-format off
  __CPROVER_requires(n <= 3)
  __CPROVER_ensures(__CPROVER_return_value == n)
// clang-format on
{
  unsigned r = 0;
  unsigned i;
  // This loop has no contract and is therefore skipped (not abstracted).
  for(unsigned j = 0; j < 2; j++)
  {
    unsigned x = 0;
    i = 0;
    // A loop with a contract nested in a loop without a contract: its write
    // set must be checked against the function's write set, which does not
    // permit assigning `g`.
    while(i < n)
      // clang-format off
      __CPROVER_assigns(i, x, g)
      __CPROVER_loop_invariant(i <= n && x == i)
      __CPROVER_decreases(n - i)
      // clang-format on
      {
        x++;
        i++;
        g = x;
      }
    r = x;
  }
  return r;
}

int main()
{
  unsigned n;
  foo(n);
  return 0;
}
