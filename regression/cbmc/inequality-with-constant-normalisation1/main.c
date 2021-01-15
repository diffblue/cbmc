#include <assert.h>

#ifdef _MSC_VER
#  define _Static_assert(x, m) static_assert(x, m)
#endif

int main()
{
  _Bool b1, b2;

  int nc = (b1 ? 1 : 2) == (b2 ? 1 : 2);
  assert(b1 != b2 || nc != 0);

  // The following are true for all values of b1, b2, and the simplifier should
  // be able to figure this out.
  _Static_assert((b1 ? 1 : 1) == (b2 ? 1 : 1), "");
  _Static_assert(((b1 ? 2 : 3) >= (b2 ? 1 : 2)) != 0, "");
  _Static_assert(((b1 ? 0 : 1) >= (b2 ? 2 : 3)) == 0, "");
  _Static_assert(((b1 ? 0 : 1) >= 2) == 0, "");
}
