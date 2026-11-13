#include <assert.h>
int x = 1, v = 2;
int main(void)
{
  // In-place swap: val and ret are the same object.
  __atomic_exchange(&x, &v, &v, __ATOMIC_SEQ_CST);
  // The correct result: x gets old v (2), v gets old x (1).
  assert(x == 2);
  assert(v == 1);
  return 0;
}
