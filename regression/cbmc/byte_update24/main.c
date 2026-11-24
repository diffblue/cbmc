#include <stdint.h>
#include <string.h>

int main()
{
  uint8_t src[8];

  uint32_t x, x_orig = x;
  size_t k, n;
  __CPROVER_assume(k < sizeof(x));
  __CPROVER_assume(n <= sizeof(x) - k);
  memcpy((uint8_t *)&x + k, src, n);
  for(size_t i = 0; i < sizeof(x); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)&x)[i] ==
        (i >= k && i < k + n ? src[i - k] : ((uint8_t *)&x_orig)[i]),
      "uint32_t: exactly bytes k..k+n-1 are copied");
  }

  uint64_t y, y_orig = y;
  size_t l, m;
  __CPROVER_assume(l < sizeof(y));
  __CPROVER_assume(m <= sizeof(y) - l);
  memcpy((uint8_t *)&y + l, src, m);
  for(size_t i = 0; i < sizeof(y); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)&y)[i] ==
        (i >= l && i < l + m ? src[i - l] : ((uint8_t *)&y_orig)[i]),
      "uint64_t: exactly bytes l..l+m-1 are copied");
  }
  return 0;
}
