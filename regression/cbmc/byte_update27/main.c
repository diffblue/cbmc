#include <stdint.h>
#include <string.h>

int main()
{
  uint32_t a[2][3], orig[2][3], src[2][3];
  memcpy(a, orig, sizeof(a));
  size_t n;
  __CPROVER_assume(n <= sizeof(a));
  memcpy(a, src, n);
  for(size_t i = 0; i < sizeof(a); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)a)[i] == (i < n ? ((uint8_t *)src)[i] : ((uint8_t *)orig)[i]),
      "exactly bytes 0..n-1 are copied");
  }
  return 0;
}
