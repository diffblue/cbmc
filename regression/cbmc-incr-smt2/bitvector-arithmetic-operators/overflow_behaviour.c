#include <limits.h>
#include <stdlib.h>

int main()
{
  int a = INT_MAX;
  int b = INT_MIN;

  __CPROVER_assert(
    a + 1 == INT_MIN, "Wrap-around to INT_MIN when adding to INT_MAX");
  __CPROVER_assert(
    b - 1 == INT_MAX, "Wrap-around to INT_MAX when subtracting from INT_MIN");
  __CPROVER_assert(a - b == -1, "INT_MAX minus INT_MIN equals -1");
}
