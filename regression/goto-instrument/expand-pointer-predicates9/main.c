#include <stdlib.h>

int main()
{
  char *x;
  __CPROVER_assume(__CPROVER_points_to_valid_memory(x));
  (void)(*x); // Should succeed
  (void)(*(x + 1)); // Should fail
  (void)(*(x - 1)); // Should fail
  return 0;
}
