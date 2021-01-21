#include <assert.h>

union U_ok {
  int x;
  int y;
} u_ok = {.x = 1, .y = 2};

#ifndef _MSC_VER
union U {
  int x;
  int y;
} u = {1, 2};

int main()
{
  assert(u_ok.y == 2);
  // the excess initializer (2) is ignored
  assert(u.x == 1);
}
#else
int main()
{
  assert(u_ok.y == 2);
}
#endif
