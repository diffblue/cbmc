#include <assert.h>

int main()
{
  int array[5];

  int *p = array;
  int *q = array + 4;

  int offset = (q - p);
  assert(offset == 4);

  --q;
  offset = (q - p);
  assert(offset == 3);

  q--;
  offset = (q - p);
  assert(offset == 2);

  q -= 1;
  offset = (q - p);
  assert(offset == 1);

  q = q - 1;
  offset = (q - p);
  assert(offset == 0);
  assert(q == p);
}
