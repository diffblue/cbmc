#include <assert.h>

// Multi-level pointer const variation: const int ** const (a const, by-value
// pointer to a NON-const pointer to const int). Top-level const is irrelevant
// to the callee and the immediate pointee `const int *` is a non-const
// pointer, so the generator redirects *pp to a fresh nondet object.
void havoc_const_pp_const_int(const int **const pp);

int main(void)
{
  int e = 5;
  const int *cpe = &e;
  const int **const pp = &cpe;

  assert(e == 5);    // baseline
  assert(**pp == 5); // baseline

  havoc_const_pp_const_int(pp);

  assert(e == 5);    // the named local 'e' is untouched: SUCCESS
  assert(**pp == 5); // *pp was redirected to a nondet object: FAILURE

  return 0;
}
