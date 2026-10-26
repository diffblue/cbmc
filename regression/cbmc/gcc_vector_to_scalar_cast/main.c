#include <assert.h>
#include <stdint.h>
#include <string.h>

#ifdef __GNUC__
typedef uint16_t u16x4 __attribute__((vector_size(8)));
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
#endif

  return 0;
}
