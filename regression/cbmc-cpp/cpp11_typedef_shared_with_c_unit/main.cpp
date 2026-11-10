#include "shared.h"
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  __CPROVER_assert(wrap(3, 0) == 4, "wrap");
  __CPROVER_assert(wrap(3, 0) == 3, "WRONG (must FAIL)");
  return 0;
}
