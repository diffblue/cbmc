#include <assert.h>
#include <stdint.h>

typedef uint16_t u16x4 __attribute__((vector_size(8)));
typedef int16_t i16x4 __attribute__((vector_size(8)));

int main(void)
{
  uint16_t a;
  int16_t b;
  u16x4 u = {a, 1, 2, 3};
  i16x4 s = {b, 1, 2, 3};

  // vector >> scalar is a logical shift for unsigned elements
  u16x4 ur = u >> 4;
  assert(ur[0] == (uint16_t)(a >> 4));

  // vector >> vector is an arithmetic shift for signed elements
  i16x4 sr = s >> (i16x4){4, 4, 4, 4};
  assert(sr[0] == (int16_t)(b >> 4));

  return 0;
}
