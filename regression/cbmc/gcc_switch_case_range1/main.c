#include <limits.h>

int main()
{
  int x;
  switch(x)
  {
  case 0:
#ifdef __GNUC__
  // empty case - GCC emits a warning, but this is still reached via
  // fall-through
  case 13 ... 12:
#endif
    __CPROVER_assert(0, "0 works");
    break;
#ifdef __GNUC__
  case 1 ... 12:
#else
  case 42:
#endif
    __CPROVER_assert(0, "... works");
    break;
  case 14:
    __CPROVER_assert(0, "13 works");
    break;
  case 15 ... INT_MAX:
    __CPROVER_assert(0, "large range works");
    break;
  default:
    __CPROVER_assert(0, "default works");
    break;
  }

  return 0;
}
