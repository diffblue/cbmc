#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

__CPROVER_bool w[8];
__CPROVER_bool v[(__CPROVER_size_t)1 << (sizeof(__CPROVER_size_t) * 8 - 2)];

void main()
{
  _Bool x[8] = {false};
  __CPROVER_bool y[8] = {false};
  bool *z = calloc(8, sizeof(bool));

  unsigned char idx;
  __CPROVER_assume(0 <= idx && idx < 8);

  assert(w[idx] == x[idx]);
  assert(x[idx] == y[idx]);
  assert(y[idx] == z[idx]);
}
