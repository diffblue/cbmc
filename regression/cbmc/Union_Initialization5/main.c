#include <assert.h>

#ifndef _MSC_VER
union U {
  int x;
  int y;
} u = {1, 2};

int main()
{
  // the excess initializer (2) is ignored
  assert(u.x == 1);
}
#else
int main()
{
}
#endif
