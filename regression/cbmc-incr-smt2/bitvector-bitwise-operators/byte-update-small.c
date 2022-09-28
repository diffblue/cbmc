#include <assert.h>
#include <stdint.h>

int main()
{
  uint8_t x[2];
  x[0] = 0;
  x[1] = 0;
  uint16_t *y = x;
  *y = 258;
  assert(x[0] == 2);
  assert(x[1] == 1);
}
