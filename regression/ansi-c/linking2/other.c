#ifndef TEST2
#  include "foo.h"
#else
inline void foo(int x)
{
  x = 0;
}
#endif

void bar(int y)
{
  foo(y);
  y = 2;
}
