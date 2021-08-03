#include <assert.h>

int main()
{
  int array[5];

  int *p = array;
  int *q = array + 4;

  int offset = (q - p);
  assert(offset == 4);

  p += 1;
  offset = (q - p);
  assert(offset == 3);

  ++p;
  offset = (q - p);
  assert(offset == 2);

  p++;
  offset = (q - p);
  assert(offset == 1);

  p = p + 1;
  offset = (q - p);
  assert(offset == 0);
  assert(p == q);
}
