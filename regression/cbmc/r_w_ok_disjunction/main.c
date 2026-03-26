int g;

// An rw_ok under a disjunction must not unconditionally constrain the pointer.
// Here rw_ok is not a top-level conjunct, so no backing object is created and
// the `p == &g` disjunct is preserved: p may still equal &g, hence the
// assertion `p != &g` has a counterexample.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  int *p;
  __CPROVER_assume(p == &g || __CPROVER_rw_ok(p, sizeof(*p)));
  __CPROVER_assert(p != &g, "p could be &g");
  return 0;
}
