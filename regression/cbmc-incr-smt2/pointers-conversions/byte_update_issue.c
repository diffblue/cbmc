#include <assert.h>
#include <stdint.h>

int main()
{
  uint32_t x = 0;
  uint8_t *ptr = (uint8_t *)(&x);
  int offset;
  __CPROVER_assume(offset >= 0 && offset < 4);
  *(ptr + offset) = 1;
  assert(x != 256);
}
