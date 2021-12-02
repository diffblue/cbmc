#include <assert.h>
#include <stdlib.h>

int main()
{
  int *p = NULL;

  assert(!__CPROVER_r_ok(p, sizeof(int)));
  assert(!__CPROVER_w_ok(p, sizeof(int)));
  assert(!__CPROVER_r_ok(p, 0));
  assert(!__CPROVER_w_ok(p, 0));

  p = malloc(sizeof(int));

  assert(__CPROVER_r_ok(p, 1));
  assert(__CPROVER_w_ok(p, 1));
  assert(__CPROVER_r_ok(p, sizeof(int)));
  assert(__CPROVER_w_ok(p, sizeof(int)));
  assert(__CPROVER_r_ok(p + 1, 0));
  assert(__CPROVER_w_ok(p + 1, 0));

  size_t n;
  char *arbitrary_size = malloc(n);

  assert(__CPROVER_r_ok(arbitrary_size, n));
  assert(__CPROVER_w_ok(arbitrary_size, n));

  assert(__CPROVER_r_ok(arbitrary_size, n + 1)); // expected to fail
  assert(__CPROVER_w_ok(arbitrary_size, n + 1)); // expected to fail
}
