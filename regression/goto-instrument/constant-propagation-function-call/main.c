#include <assert.h>
int ab, bc;
int f(int x)
{
  ab = 1 + 1 + 1 + 1;
  bc = ab + x;
  return ab + bc;
}
int main()
{
  int a;
  a = -4;
  int b;
  b = nondet();
  a = f(a);
  assert(!(0 <= a && a < 5 && 0 <= b && b < 5));
}
