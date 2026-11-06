#include <stdint.h>
#include <string.h>

// Byte update with symbolic size must not skip the last element when
// the size is a multiple of the element size (GitHub issue #9170).
int main()
{
  unsigned n;
  __CPROVER_assume(n == 4 || n == 8);
  uint32_t src[2] = {0x11111111u, 0x22222222u};
  uint32_t dst[2] = {0, 0};
  memcpy(dst, src, n);
  __CPROVER_assert(dst[0] == 0x11111111u, "dst[0] fully copied");
  __CPROVER_assert(n != 8 || dst[1] == 0x22222222u, "dst[1] fully copied");
}
