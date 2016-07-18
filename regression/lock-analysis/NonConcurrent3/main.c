// accesses to x, y are non-concurrent

#include <pthread.h>

int x, y;

void func3()
{
  x = 2;
}

void func2()
{
  x = 1;
}

void func1()
{
  func2();
}

int main()
{
  func1();
  func3();

  return 0;
}

