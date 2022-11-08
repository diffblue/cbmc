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
  assert(x[0] == 256ul);
  assert(x[0] == 0ul);
  assert(x[1] == 0ul);
  assert(x[2] == 0ul);
}
