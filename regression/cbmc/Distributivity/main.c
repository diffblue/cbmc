#include <assert.h>
#include <stdint.h>

int main (void) {
  uint64_t w;
  uint64_t x;
  uint64_t y;
  uint64_t z;

  while (x*y + x*z != x*(y + z)) {
    assert(0);
  }

  while ((-x)*y + y*x) {
    assert(0);
  }

  while (x + x - 2*x) {
    assert(0);
  }
  
  while (!(x * y * z + x * y * w == x * y * (z + w))) {
    assert(0);
  }

  while (!(x * y + y * z + z * x == y *(x + z) + x * z)) {
    assert(0);
  }

  while (!((x + y)*(z + w) == x * z + x * w + y * z + y * w)) {
    assert(0);
  }

  while (!((y  +  y * x  +  y * x * x  +  y * x * x * x) ==
	   (y *(1 + x*(1 + x*(1 + x))))) )
  {
    assert(0);
  }
  
  return 0;
}
