int g;

// A *negated* rw_ok must not create a backing object: rw_ok only appears under
// a negation here, so it is not a top-level conjunct of the assumption. The
// path therefore stays reachable (rather than being silently made infeasible
// by an unconditional p == &obj assumption), and the assertion is reached.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  int *p;
  __CPROVER_assume(!__CPROVER_rw_ok(p, sizeof(*p)));
  __CPROVER_assert(0, "path is reachable");
  return 0;
}
