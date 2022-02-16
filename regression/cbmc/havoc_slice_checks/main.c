// Here we test that __CPROVER_havoc_slice checks fail as expected
#include <stdint.h>
#include <stdlib.h>

int main()
{
  // invalid pointer
  int *invalid_ptr;
  __CPROVER_havoc_slice(invalid_ptr, 1);

  // null pointer
  int *null_ptr = NULL;
  __CPROVER_havoc_slice(null_ptr, 1);

  int a[4];

  // positive size but out of bounds
  __CPROVER_havoc_slice(&a[2], 3 * sizeof(*a));

  // positive size but out of bounds
  __CPROVER_havoc_slice(a, 5 * sizeof(*a));

  // pointer invalidated by overflow
  __CPROVER_havoc_slice(&a[0] + 6, sizeof(*a));

  // pointer invalidated by underflow
  __CPROVER_havoc_slice(&a[0] - 1, sizeof(*a));

  // negative size
  __CPROVER_havoc_slice(&a[0], -2);
}
