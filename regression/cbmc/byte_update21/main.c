#include <stdint.h>
#include <string.h>

int main()
{
  uint32_t src[4], dst[4], d[4];
  memcpy(d, dst, sizeof(d));

  // Copy to offset 1, i.e., starting in the middle of element d[0].
  size_t n;
  __CPROVER_assume(n < sizeof(d));
  memcpy((uint8_t *)d + 1, src, n);

  for(size_t i = 0; i < sizeof(d); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)d)[i] ==
        (i >= 1 && i < 1 + n ? ((uint8_t *)src)[i - 1] : ((uint8_t *)dst)[i]),
      "exactly bytes 1..n are copied");
  }
  return 0;
}
