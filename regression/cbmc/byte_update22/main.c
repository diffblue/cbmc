#include <stdint.h>
#include <string.h>

struct S
{
  uint32_t a;
  uint16_t b;
  uint32_t c;
};

union U
{
  uint32_t a;
  uint64_t b;
};

int main()
{
  uint8_t src[sizeof(struct S)];

  struct S s, s_orig;
  memcpy(&s, &s_orig, sizeof(s));
  size_t n;
  __CPROVER_assume(n <= sizeof(s) - 1);
  memcpy((uint8_t *)&s + 1, src, n);
  for(size_t i = 0; i < sizeof(s); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)&s)[i] ==
        (i >= 1 && i < 1 + n ? src[i - 1] : ((uint8_t *)&s_orig)[i]),
      "struct: exactly bytes 1..n are copied");
  }

  union U u, u_orig;
  memcpy(&u, &u_orig, sizeof(u));
  size_t m;
  __CPROVER_assume(m <= sizeof(u) - 2);
  memcpy((uint8_t *)&u + 2, src, m);
  for(size_t i = 0; i < sizeof(u); ++i)
  {
    __CPROVER_assert(
      ((uint8_t *)&u)[i] ==
        (i >= 2 && i < 2 + m ? src[i - 2] : ((uint8_t *)&u_orig)[i]),
      "union: exactly bytes 2..m+1 are copied");
  }
  return 0;
}
