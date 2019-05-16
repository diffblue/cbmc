#include <assert.h>

int array[] = {1, 2, 3};
int *p;
int *q;

void initialize()
{
  p = &(array[1]);
  q = array + 1;
  array[0] = 4;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(p == &(array[1]));
  assert(p == q);
  assert(*p == *q);
  assert(array[0] != *p);
  *p = 4;
  assert(array[0] == *p);
}
