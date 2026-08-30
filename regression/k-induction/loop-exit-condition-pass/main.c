// Polarity guard for the loop-exit assumption inserted by k-induction.
// The assertion is *after* the loop, so it is only reachable through the
// loop-exit assume(loop has exited). With the correct exit condition
// (i >= 2), this true property is verified; an inverted assume would prune
// the real exit state.
int main()
{
  unsigned i = 0;
  while(i < 2)
    i++;
  __CPROVER_assert(i >= 2, "i >= 2 holds at loop exit");
}
