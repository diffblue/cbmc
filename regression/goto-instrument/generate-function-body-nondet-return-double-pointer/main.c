#include <assert.h>
#include <stdlib.h>

int **func();

void main()
{
  int **p = func();

  assert(p != NULL);
  assert(*p != NULL);

  assert(**p == 0);
  assert(**p != 0);
}
