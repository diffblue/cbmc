#include <stdint.h>

// Violation direction for the pointer-containing-object dispatch case (see
// main.c): p->q does equal &x, so asserting p->q != &x must FAIL. This
// confirms the skipped pointer-containing candidate is still offered/resolved
// and the solver does not miss the model (no unsound "no target").

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
  __CPROVER_assert(p->q != &x, "expected to FAIL: p->q can equal &x");
}
