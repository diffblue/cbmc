#include <pthread.h>

int func1() { return 0; }
int func2() { return 1; }

int func3()
{
  int i;

  i = 0;

  if (i) {
    return 0;
  } else {
    return 1;
  }
}

void func4() {}

int func5() { return 3; }

int main()
{
  int i;

  i = i + func1() + func2();

  i = func3();

  func4();

  func5();

  return 0;
}

