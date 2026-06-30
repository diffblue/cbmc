#include <stdint.h>

// Regression for the dispatch in value_set_dereferencet that skips
// pointer-containing objects as address-based dispatch candidates (with the
// rationale that the solver's backward-constraint refinement resolves them).
// Here an opaque integer address is constrained to point at a
// pointer-containing global; the dereference must still resolve to that
// global and read its pointer field correctly -- i.e. the skipped candidate
// is NOT silently dropped. The proving direction (this file) shows the value
// is read precisely; the violation direction (main-violation.c) shows the
// solver still finds the model, so no bug is missed.

struct S
{
  int *q;
} g;
int x = 5;
uint64_t nondet_uint64_t(void);

void main()
{
  g.q = &x;
  uint64_t rd = nondet_uint64_t();
  __CPROVER_assume(rd == (uint64_t)&g);
  struct S *p = (struct S *)rd;
  __CPROVER_assert(p->q == &x, "deref into pointer-containing global is sound");
}
