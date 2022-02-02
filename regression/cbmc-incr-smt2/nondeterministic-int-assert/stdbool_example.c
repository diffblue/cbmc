#include <stdbool.h>

int main()
{
  int x, y;
  bool equal = x == y;
  __CPROVER_assert(equal, "Assert of integer equality.");
  __CPROVER_assert(!equal, "Assert of not integer equality.");
  return 0;
}
