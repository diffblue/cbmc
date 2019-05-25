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

  assert(p == q);
  assert(*p == *q);
  *p = 4;
  q = q - 1;
  assert(*q == *p);
}
