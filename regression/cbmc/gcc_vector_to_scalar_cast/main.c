#include <assert.h>
#include <stdint.h>
#include <string.h>

#ifdef __GNUC__
typedef uint16_t u16x4 __attribute__((vector_size(8)));
typedef int8_t i8x8 __attribute__((vector_size(8)));
typedef float f32x2 __attribute__((vector_size(8)));
typedef __CPROVER_fixedbv[32][16] fixed;
typedef fixed fixedx2 __attribute__((vector_size(8)));
#endif

int main(void)
{
#ifdef __GNUC__
  uint16_t a;
  u16x4 u = {a, 1, 2, 3};

  // a cast from a vector to a scalar of the same size reinterprets its bits
  uint64_t x = (uint64_t)u;
  uint64_t y;
  memcpy(&y, &u, sizeof(y));
  assert(x == y);

  // likewise with signed elements and a signed scalar
  int8_t b;
  i8x8 s = {b, -2, 3, -4, 5, -6, 7, -8};
  int64_t t = (int64_t)s;
  int64_t t2;
  memcpy(&t2, &s, sizeof(t2));
  assert(t == t2);

  // and with floating-point or fixed-point elements
  float c;
  f32x2 f = {c, 1.0f};
  uint64_t g = (uint64_t)f;
  uint64_t g2;
  memcpy(&g2, &f, sizeof(g2));
  assert(g == g2);

  fixed d;
  fixedx2 h = {d, 2};
  uint64_t k = (uint64_t)h;
  uint64_t k2;
  memcpy(&k2, &h, sizeof(k2));
  assert(k == k2);
#endif

  return 0;
}
