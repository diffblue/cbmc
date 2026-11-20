#include <stdint.h>
#include <string.h>

int main()
{
  uint32_t src[4], dst[4], d[4];
  memcpy(d, dst, sizeof(d));

  size_t n;
  __CPROVER_assume(n <= sizeof(d));
  memcpy(d, src, n);

  for(size_t i = 0; i < sizeof(d); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)d)[i] == (i < n ? ((uint8_t *)src)[i] : ((uint8_t *)dst)[i]),
      "exactly bytes 0..n-1 are copied");
  }
  return 0;
}
