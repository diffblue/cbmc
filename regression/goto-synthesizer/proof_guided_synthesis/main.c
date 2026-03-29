// Test that proof-relevant variables help guide synthesis.
// The loop increments x and y, but only x matters for the assertion.
// The proof explanation should identify x as proof-relevant,
// helping the synthesizer focus on x rather than y.
int main()
{
  unsigned x = 0;
  unsigned y = 0;
  unsigned n;
  __CPROVER_assume(n > 0 && n < 10);

  while(x < n)
  {
    x++;
    y++;
  }

  __CPROVER_assert(x == n, "x equals n after loop");
}
