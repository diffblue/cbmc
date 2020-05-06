#include <assert.h>
#include <stdlib.h>

char c1;

void main()
{
  // We check the conditions for a pointer to global static memory (p1), a
  // pointer to local memory (p2), and a pointer to dynamic memory (p3).
  // For each pointer, we check:
  // (1) whether it is unsafe to access one byte more than was allocated
  // (2) whether it is unsafe to access one byte before the allocated memory
  // (3) whether it is unsafe to access one byte after the allocated memory

  char c2;

  char *p1 = &c1;

  assert(!__CPROVER_r_ok(p1, 2));
  assert(!__CPROVER_r_ok(p1 - 1, 1));
  assert(!__CPROVER_r_ok(p1 + 1, 1));

  char *p2 = &c2;

  assert(!__CPROVER_r_ok(p2, 2));
  assert(!__CPROVER_r_ok(p2 - 1, 1));
  assert(!__CPROVER_r_ok(p2 + 1, 1));

  char *p3 = malloc(1);

  assert(!__CPROVER_r_ok(p3, 2));
  assert(!__CPROVER_r_ok(p3 - 1, 1));
  assert(!__CPROVER_r_ok(p3 + 1, 1));
}
