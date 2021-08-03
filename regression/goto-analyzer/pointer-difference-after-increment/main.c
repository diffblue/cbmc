#include <assert.h>

int main()
{
  int array[5];

  int *p = array;
  int *q = p + 1;

  assert(q - p == 1);
  assert(q != p);

  ++p;
  assert(q - p == 0);
  assert(q == p);
}
