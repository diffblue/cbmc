// _BitInt is a C23 feature
#include <assert.h>

int main()
{
  // pointers
  _BitInt(3) x, *p = &x;
  *p = 1;

  return 0;
}
