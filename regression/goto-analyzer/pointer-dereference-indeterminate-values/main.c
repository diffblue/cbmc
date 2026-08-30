#include <assert.h>

int main()
{
  int unknown;
  int a = 10;

  int *p = &a;

  if(unknown)
    a = 15;

  int q = *p;

  assert(q == a);

  // q is in [10, 15], so this assertion is provably false (FAILURE).  If a
  // regression let the dereference of *p silently go to top, q would be
  // unconstrained and this would become UNKNOWN instead, so the probe guards
  // against losing the dereferenced value.
  assert(q == 5);
}
