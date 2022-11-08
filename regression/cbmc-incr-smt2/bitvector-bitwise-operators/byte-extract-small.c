#include <assert.h>
#include <stdint.h>

int main()
{
  uint8_t x[2];
  x[0] = 1u;
  x[1] = 1u;
  uint16_t *y = x;
  uint16_t z = *y;
  assert(z == 257);
}
