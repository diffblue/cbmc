#include <assert.h>
#include <stdint.h>

int main()
{
  uint16_t x;
  uint8_t *y = &x;
  assert(y[0] == 0);
}
