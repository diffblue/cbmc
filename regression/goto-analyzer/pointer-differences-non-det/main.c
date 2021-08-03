#include <assert.h>

int main()
{
  int non_det;
  int array[5];
  array[0] = 1;
  array[1] = 2;
  array[2] = 4;
  array[3] = 8;
  array[4] = 16;

  int *p = array;
  if(non_det)
    ++p;
  int *q = array + 4;
  if(non_det)
    --q;

  int offset = (q - p);
  assert(offset == 1);
  assert(offset == 2);
  assert(offset == 3);
  assert(offset == 4);
  assert(offset == 5);

  assert(offset >= 2 && offset <= 4);

  assert(offset != 1);
  assert(offset != 2);
  assert(offset != 3);
  assert(offset != 4);
  assert(offset != 5);
}
