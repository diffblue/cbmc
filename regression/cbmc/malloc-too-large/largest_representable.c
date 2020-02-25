#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  int *p = malloc(__CPROVER_max_malloc_size); // try to allocate exactly the max

  return 0;
}
