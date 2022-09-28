#include <assert.h>
#include <stdint.h>

int main()
{
  uint16_t x = 0;
  uint8_t *y = &x;
  y[1] = 1;
  assert(x == 256);
}
