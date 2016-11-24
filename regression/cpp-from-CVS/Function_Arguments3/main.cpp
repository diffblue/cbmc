#include <cassert>

int global;

// these are in fact the same
void f(const int i)
{
  global=10;
}

void f(int i);

// the following two are *different*!
void g(int *p)
{
  global=20;
}

void g(const int *p)
{
  global=30;
}

int main()
{
  f(0);
  assert(global==10);
  
  g((int *)0);
  assert(global==20);

  g((const int *)0);
  assert(global==30);
}
