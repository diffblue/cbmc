#include <stddef.h>

int main(void)
{
  short a[3][256];
  size_t j, k;
  __CPROVER_assume(j < 3 && k < 256);
  // clang-format off
  __CPROVER_assume(__CPROVER_forall {
    size_t x;
    x < 3 ==> __CPROVER_forall {
      size_t y;
      y < 256 ==> a[x][y] < 3329
    }
  });
  // clang-format on
  __CPROVER_assert(a[j][k] < 3329, "bound");
  return 0;
}
