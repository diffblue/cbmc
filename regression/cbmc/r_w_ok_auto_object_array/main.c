#include <assert.h>
#include <stdlib.h>

// Tests that auto-objects created via rw_ok work with array operations.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  size_t n = 3;

  unsigned int *a;
  __CPROVER_assume(__CPROVER_rw_ok(a, n * sizeof(*a)));
  assert(a);

  unsigned int *old_a;
  __CPROVER_assume(__CPROVER_rw_ok(old_a, n * sizeof(*old_a)));
  assert(old_a);

  __CPROVER_array_copy(old_a, a);
  assert(__CPROVER_array_equal(old_a, a));

  for(size_t i = 0; i < n; i++)
  {
    a[i] += 1;
  }

  assert(__CPROVER_forall {
    size_t i;
    i<n ==> a[i] == (old_a[i] + 1)
  });
}
