#include <assert.h>

#ifndef __GNUC__
void __atomic_clear(_Bool *, int);
#endif

int main()
{
  _Bool n;
  __atomic_clear(&n, 0);
  assert(0);
  return 0;
}
