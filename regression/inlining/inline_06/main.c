#include <assert.h>

int x;

inline void f()
{
  x += 1;

  if(x < 10)
    f();
}

inline void h()
{
  x += 1;
  if(x < 20)
    g();
}

inline void g()
{
  x += 1;
  h();
}

int main()
{
  // direct recursion
  x = 0;
  f();
  assert(x == 10);

  // indirect recursion
  x = 0;
  g();
  assert(x == 20);
}

