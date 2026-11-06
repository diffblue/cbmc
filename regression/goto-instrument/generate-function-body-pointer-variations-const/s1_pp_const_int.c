#include <assert.h>

// Multi-level pointer const variation: const int ** (pointer to pointer to
// const int). The immediate pointee type is `const int *` -- a NON-const
// pointer -- so the havoc generator reinitialises *pp to a fresh nondet
// object. The deep `const int` is therefore not protected: reading through the
// (now redirected) pointer chain may observe a different value.
void havoc_pp_const_int(const int **pp);

int main(void)
{
  int a = 1;
  const int *cpa = &a;
  const int **pp = &cpa;

  assert(a == 1);    // baseline
  assert(**pp == 1); // baseline

  havoc_pp_const_int(pp);

  assert(a == 1);    // the named local 'a' is never reached by havoc: SUCCESS
  assert(**pp == 1); // *pp was redirected to a nondet object: FAILURE

  return 0;
}
