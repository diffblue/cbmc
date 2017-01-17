#include <assert.h>

int x;

// first pair

void g1()
{
  x += 2;
  f1();
}

void f1()
{
  x += 1;
  g1();
}

// second pair

void g2()
{
  x += 2;
  f2();
}

void f2()
{
  x += 1;
  g2();
}

int main()
{
  f1();
  x = 0;
  g1();
  assert(x == 2);

  g2();
  x = 0;
  g2();
  assert(x == 3);
}

