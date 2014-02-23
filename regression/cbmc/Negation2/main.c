#include <assert.h>
#include <stdint.h>

void f00 (unsigned int g) {
  uint64_t k = ((uint64_t)~g);
  uint64_t l = (0xFF00000000ull & k);

  assert(l == 0);
}

int main()
{
  f00(0);
}

