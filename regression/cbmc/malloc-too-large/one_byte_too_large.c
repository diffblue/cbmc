#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  // try to allocate the smallest violating amount
  int *p = malloc(__CPROVER_max_malloc_size + 1);
  assert(p);

  return 0;
}
