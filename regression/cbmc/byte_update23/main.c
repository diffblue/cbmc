#include <stdint.h>
#include <string.h>

int main()
{
  uint32_t src[4], orig[4], d[4];
  memcpy(d, orig, sizeof(d));

  size_t k, n;
  __CPROVER_assume(k < sizeof(d));
  __CPROVER_assume(n <= sizeof(d) - k);
  memcpy((uint8_t *)d + k, src, n);

  for(size_t i = 0; i < sizeof(d); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)d)[i] ==
        (i >= k && i < k + n ? ((uint8_t *)src)[i - k] : ((uint8_t *)orig)[i]),
      "exactly bytes k..k+n-1 are copied");
  }
  return 0;
}
