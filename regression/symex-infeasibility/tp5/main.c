#include <assert.h>

int f(int x) {
  return 2*x;
}

int g(int x) {
  int y = x;

  while (x--) {
    y++;
  }

  return y;
}

int main(void) {
  unsigned int x;

  __CPROVER_assume(x < 50);

  if (x >= 0) {
    assert(f(x) == g(x));
  }
}
