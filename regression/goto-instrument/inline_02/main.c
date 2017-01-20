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

int main()
{
  x = 0;
  f(3, 7);
  assert(x == 22);
}

