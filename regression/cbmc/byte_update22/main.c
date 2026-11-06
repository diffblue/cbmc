#include <stdint.h>
#include <string.h>

// Byte update with symbolic size at a non-zero offset into a scalar
// must not overwrite bytes beyond the size (GitHub issue #9173).
int main()
{
  unsigned n;
  __CPROVER_assume(n == 1 || n == 2);
  unsigned char src[2] = {0xAA, 0xBB};
  uint32_t x = 0x44332211u, orig = x;
  memcpy((unsigned char *)&x + 1, src, n);
  unsigned char *b = (unsigned char *)&x, *o = (unsigned char *)&orig;
  __CPROVER_assert(b[0] == o[0], "byte 0 unchanged");
  __CPROVER_assert(b[1] == 0xAA, "byte 1 copied");
  __CPROVER_assert(n != 1 || b[2] == o[2], "byte 2 unchanged when n == 1");
  __CPROVER_assert(b[3] == o[3], "byte 3 unchanged");
}
