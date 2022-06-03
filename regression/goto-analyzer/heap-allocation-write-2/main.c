#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int) * 5);
  int *q = malloc(sizeof(int) * 10);

  int *pp = p;

  *p = 10;
  ++p;
  *p = 20;

  q[0] = 100;
  q[99] = 101;

  assert(pp[0] == 10);
  assert(pp[1] == 20);
  assert(q[0] == 100);
  assert(q[99] == 101);
}
