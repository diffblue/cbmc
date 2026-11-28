#include <stdint.h>
#include <string.h>

uint8_t nondet_uint8_t(void);

int main()
{
  // memset into an array of uint64_t at a symbolic offset
  uint64_t w[3], w_orig[3];
  memcpy(w, w_orig, sizeof(w));
  size_t k, n;
  __CPROVER_assume(k < sizeof(w) && n <= sizeof(w) - k);
  memset((uint8_t *)w + k, 0x5a, n);
  for(size_t i = 0; i < sizeof(w); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)w)[i] ==
        (i >= k && i < k + n ? 0x5a : ((uint8_t *)w_orig)[i]),
      "memset: exactly bytes k..k+n-1 are set");
  }

  // memset with a size of a narrower type, as reported on #9187
  uint32_t e[4] = {1, 1, 1, 1};
  uint8_t m = nondet_uint8_t();
  __CPROVER_assume(m == 16);
  memset(e, 0, m);
  __CPROVER_assert(
    e[0] == 0 && e[1] == 0 && e[2] == 0 && e[3] == 0, "memset: all bytes set");

  return 0;
}
