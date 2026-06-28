#include <assert.h>

int main()
{
  int x = 1;
  int y = 2;
  int *p = &x;
  int *q = &y;

  // address-of and pointer comparison
  assert(p == &x);
  assert(q == &y);
  assert(p != q);

  // pointer arithmetic
  int arr[3] = {10, 20, 30};
  int *r = arr;
  assert(*r == 10);
  assert(*(r + 1) == 20);
  assert(*(r + 2) == 30);

  return 0;
}
