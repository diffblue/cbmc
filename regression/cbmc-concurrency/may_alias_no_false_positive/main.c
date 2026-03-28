// Verify that may-alias does NOT trigger for non-shared pointers.
// This sequential program must verify successfully — no false positives.
#include <assert.h>
#include <stdlib.h>

int main(void)
{
  int x = 42;
  int *p = &x;
  assert(*p == 42);

  int *q = malloc(sizeof(int));
  if(q)
  {
    *q = 99;
    assert(*q == 99);
  }

  int arr[3] = {1, 2, 3};
  int *r = &arr[1];
  assert(*r == 2);
}
