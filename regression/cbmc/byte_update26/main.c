#include <stdint.h>
#include <string.h>

struct P
{
  uint16_t a, b;
};

int main()
{
  uint8_t src[24];

  // memmove into an array of uint16_t at a symbolic offset
  uint16_t h[6], h_orig[6];
  memcpy(h, h_orig, sizeof(h));
  size_t k, n;
  __CPROVER_assume(k < sizeof(h) && n <= sizeof(h) - k);
  memmove((uint8_t *)h + k, src, n);
  for(size_t i = 0; i < sizeof(h); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)h)[i] ==
        (i >= k && i < k + n ? src[i - k] : ((uint8_t *)h_orig)[i]),
      "memmove: exactly bytes k..k+n-1 are copied");
  }

  // memcpy into an array of structs, starting at byte 1
  struct P p[4], p_orig[4];
  memcpy(p, p_orig, sizeof(p));
  size_t m;
  __CPROVER_assume(m <= sizeof(p) - 1);
  memcpy((uint8_t *)p + 1, src, m);
  for(size_t i = 0; i < sizeof(p); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)p)[i] ==
        (i >= 1 && i < 1 + m ? src[i - 1] : ((uint8_t *)p_orig)[i]),
      "array of structs: exactly bytes 1..m are copied");
  }

  // __CPROVER_array_replace with a source of symbolic size
  uint32_t d[4], d_orig[4];
  memcpy(d, d_orig, sizeof(d));
  size_t l;
  __CPROVER_assume(l >= 1 && l <= sizeof(d));
  uint8_t s[l];
  __CPROVER_array_replace((uint8_t *)d, s);
  for(size_t i = 0; i < sizeof(d); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)d)[i] == (i < l ? s[i] : ((uint8_t *)d_orig)[i]),
      "array_replace: exactly bytes 0..l-1 are replaced");
  }

  return 0;
}
