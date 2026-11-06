#include <stdint.h>
#include <string.h>

// Byte update with symbolic size starting at a non-zero offset inside
// an element must write the following element (GitHub issue #9172).
int main()
{
  unsigned n;
  __CPROVER_assume(n == 3 || n == 4);
  unsigned char src[4] = {0xAA, 0xBB, 0xCC, 0xDD};
  uint32_t dst[2] = {0, 0};
  memcpy((unsigned char *)dst + 2, src, n);
  unsigned char *b = (unsigned char *)dst;
  __CPROVER_assert(b[2] == 0xAA && b[3] == 0xBB, "first element copied");
  __CPROVER_assert(b[4] == 0xCC, "byte 4 copied");
  __CPROVER_assert(n != 4 || b[5] == 0xDD, "byte 5 copied");
}
