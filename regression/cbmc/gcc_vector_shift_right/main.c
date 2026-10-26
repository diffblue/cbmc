#include <assert.h>
#include <stdint.h>

#ifdef __GNUC__
typedef uint16_t u16x4 __attribute__((vector_size(8)));
typedef int16_t i16x4 __attribute__((vector_size(8)));
#endif

int main(void)
{
#ifdef __GNUC__
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
#endif

  return 0;
}
