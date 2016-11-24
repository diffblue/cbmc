#include <assert.h>
#include <stdint.h>

union u
{
  uint32_t x;
   int32_t y;
   int8_t  z[4];
};

union u pass_through_union (int32_t q)
{
  union u un;

  un.z[0] = 0;
  un.y = q;

  return un;
}

int main (void)
{
  int32_t q;

  __CPROVER_assume(q > 0);

  union u un = pass_through_union(q);

  assert(q == un.x);

  return 1;
}
