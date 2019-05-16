#include <assert.h>

int x;
int *p1;
int **p2;

void initialize()
{
  x = 3;
  p1 = &x;
  p2 = &p1;
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(&p1 == *p2);
  assert(*p2 == p1);
  assert(*p1 == 3);
  assert(*p2 == &x);
  assert(**p2 == x);

  return 0;
}
