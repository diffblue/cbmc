#include <assert.h>
#include <stdint.h>

int main()
{
  uint32_t x = 0u;
  uint8_t *ptr = (uint8_t *)(&x);
  uint32_t offset;
  __CPROVER_assume(offset >= 0u && offset < 4u);
  *(ptr + offset) = 1u;
  assert(x != 256u);
}
