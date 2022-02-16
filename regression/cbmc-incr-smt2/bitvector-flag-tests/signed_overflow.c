#include <limits.h>

int main()
{
  int x = INT_MAX;
  int y;
  int z = x + y;

  __CPROVER_assert(z < INT_MIN, "This assertion is falsifiable");
}
