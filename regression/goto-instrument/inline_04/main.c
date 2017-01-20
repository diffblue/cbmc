#include <assert.h>

int x;

int h() {
  return 9;
}

void g(int i) {
  x += i + h(); // += 12
}

void f(int i, int j) {
  g(i);
  x += i + j; // +=10
}

void other_func() {}

int main()
{
  x = 0;
  f(3, 7);
  other_func();
  
  assert(x == 22);
}

