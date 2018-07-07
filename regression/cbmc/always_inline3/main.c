#include <assert.h>

#ifndef __GNUC__
#define __attribute__(x)
#endif

static inline __attribute__((__always_inline__)) void func(int *val)
{
  if(*val < 0)
  {
    *val = 1;
    return;
  }
  else
  {
    *val = 1;
    return;
  }
}

static inline int func2(int *p)
{
  func(p);
  return *p;
}

int main()
{
  int x;
  assert(func2(&x) == 1);
  return 0;
}
