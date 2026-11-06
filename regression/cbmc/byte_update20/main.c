#include <stdint.h>
#include <string.h>

// Byte update with symbolic size must write the partially covered
// last array element (GitHub issue #9171).
int main()
{
  unsigned n;
  __CPROVER_assume(n == 5 || n == 6);
  unsigned char src[6] = {0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF};
  uint32_t dst[2] = {0, 0};
  memcpy(dst, src, n);
  unsigned char *b = (unsigned char *)dst;
  __CPROVER_assert(b[4] == 0xEE, "byte 4 copied");
  __CPROVER_assert(n != 6 || b[5] == 0xFF, "byte 5 copied");
}
