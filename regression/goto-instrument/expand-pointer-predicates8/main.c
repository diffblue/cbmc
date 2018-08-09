#include <stdlib.h>

int main()
{
  int *x;
  int *y;
  __CPROVER_assume(__CPROVER_points_to_valid_memory(x, 2 * sizeof(int)));
  __CPROVER_assume(__CPROVER_points_to_valid_memory(y, 2 * sizeof(int) - 1));
  (void)(x[0]); // Should succeed
  (void)(x[1]); // Should succeed
  (void)(x[2]); // Should fail
  (void)(x[-1]); // Should fail
  (void)(y[0]); // Should succeed
  (void)(y[1]); // Should fail
  return 0;
}
