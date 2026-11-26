#include <assert.h>

// An integer expression with value 0 that has side effects is not a null
// pointer constant; converting it to a pointer must keep the side effects.
int main(void)
{
  int x = 0;
  int *p = 0;
  // comparison of a pointer with an integer expression that has value 0
  int r = p == x++ * 0;
  assert(x == 1);
  assert(r);
  // implicit conversion of such an expression to a pointer
  int *q = x++ * 0;
  assert(x == 2);
  assert(q == 0);
  // explicit conversion
  int *s = (int *)(x++ * 0);
  assert(x == 3);
  assert(s == 0);
  // the conditional operator
  int *t = x ? (x++ * 0) : p;
  assert(x == 4);
  assert(t == 0);
  return 0;
}
