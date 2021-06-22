#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  size_t size;
  size = 1<<31; // Chosen to be beyond the coded limit in cbmc source
  uint8_t *ptr = malloc(size);
  __CPROVER_assume(ptr != NULL);
  uint8_t *ptr_end = ptr + size;
  assert(ptr <= ptr_end);
}
