#include <assert.h>
#include <stdint.h>

int main()
{
  uint16_t x[3];
  x[0] = 0;
  x[1] = 0;
  x[2] = 0;
  uint8_t *c = x;
  c[1] = 1;
  assert(x[0] == 256);
  assert(x[0] == 0);
  assert(x[1] == 0);
  assert(x[2] == 0);
  uint16_t between = c[1];
  assert(between == 1);
}
