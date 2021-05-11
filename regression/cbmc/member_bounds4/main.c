#include <assert.h>
#include <inttypes.h>

union U {
  uint8_t a[4];
};

int main()
{
  uint32_t x[2] = {0xDEADBEEF, 0xDEADBEEF};
  union U *u = x;
  uint8_t c4 = u->a[4];

  unsigned word = 1;
  if(*(char *)&word == 1)
    assert(c4 == 0xEF); // little endian
  else
    assert(c4 == 0xDE); // big endian
}
