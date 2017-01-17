#include <assert.h>

int x;

void f()
{
  x += 1;

  if(x < 10)
    f();
}

void h()
{
  x += 1;
  if(x < 20)
    g();
}

void g()
{
  x += 1;
  h();
}

int main()
{
  // direct recursion
  x = 0;
  f();
  assert(x == 1);

  // indirect recursion
  x = 0;
  g();
  assert(x == 2);
}

