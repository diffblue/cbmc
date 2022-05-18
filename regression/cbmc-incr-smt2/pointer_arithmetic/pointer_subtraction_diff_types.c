#include <stdlib.h>
int main()
{
  int *x = malloc(sizeof(int));
  float *y = x + 3;
  int z = y - x;
  __CPROVER_assert(y == x, "expected failure after pointer manipulation");
  __CPROVER_assert(z == 3, "expected successful after pointer manipulation");
  __CPROVER_assert(z != 3, "expected failure after pointer manipulation");
}
