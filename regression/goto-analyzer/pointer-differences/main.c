#include <assert.h>

int main()
{
  int array[5];
  array[0] = 1;
  array[1] = 2;
  array[2] = 4;
  array[3] = 8;
  array[4] = 16;

  int *p = array;
  int *q = array + 4;

  int offset = (q - p);
  assert(offset == 4);
  offset = ((q + 1) - (p + 2));
  assert(offset == 3);
  offset = ((q - 1) - (p + 2));
  assert(offset == 1);
  offset = ((q - 2) - (p + 2));
  assert(offset == 0);

  q = (p + 2);
  offset = q - p;
  assert(offset == 2);
  assert(q == p);

  offset = q - p;
  assert(offset == 0);
}
