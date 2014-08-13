#include <assert.h>
#include <stdint.h>

union u
{
  uint32_t x;
   int32_t y;
   int8_t  z[4];
};

union u pass_through_union (uint32_t q)
{
  union u un;

  un.z[0] = 0x0;
  un.y = q;
  un.z[3] = 0x0;
  un.z[0] = 0x0;

  return un;
}

int main (void)
{
  uint32_t q;

  __CPROVER_assume((q & q - 1) == 0);
  __CPROVER_assume(256 <= q && q <= (1 << 23));

  union u un = pass_through_union(q);

  assert(q == un.y);

  return 1;
}
