#include <assert.h>

#ifndef __GNUC__
#define __attribute__(x)
#endif

static inline __attribute__((__always_inline__)) int func(int *val)
{
  switch(*val)
  {
    case 1:
      return *val + 1;
    case 2:
      return *val + 2;
  }

  return *val;
}

static inline int func2(int *p)
{
  return func(p);
}

int main()
{
  int x = 1;
  assert(func2(&x) == 2);
  return 0;
}
