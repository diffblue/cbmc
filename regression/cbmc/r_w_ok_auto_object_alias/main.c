#include <assert.h>
#include <stdlib.h>

// Tests that auto-object assumptions propagate to aliases.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  unsigned int *a;
  unsigned int *b;
  unsigned int *c;

  // create alias before assumption
  b = a;
  __CPROVER_assume(__CPROVER_rw_ok(a, sizeof(*a)));

  // create alias after assumption
  c = a;

  assert(a);
  assert(b);
  assert(c);

  // dereference through aliases should pass pointer checks
  assert(*b == *a);
  assert(*c == *a);

  *a = 1;
  // assertions and pointer checks should pass for aliases
  assert(*b == 1);
  assert(*c == 1);
}
