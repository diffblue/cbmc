#include <assert.h>

// Multi-level pointer const variation: int ** const (a const, by-value pointer
// to a non-const pointer to int). Top-level const on a by-value parameter is
// irrelevant to the callee, and the immediate pointee `int *` is non-const, so
// the generator redirects *pp to a fresh nondet object.
void havoc_const_pp_int(int **const pp);

int main(void)
{
  int c = 3;
  int *pc = &c;
  int **const pp = &pc;

  assert(c == 3);    // baseline
  assert(**pp == 3); // baseline

  havoc_const_pp_int(pp);

  assert(c == 3);    // the named local 'c' is untouched: SUCCESS
  assert(**pp == 3); // *pp was redirected to a nondet object: FAILURE

  return 0;
}
