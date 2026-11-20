#include <string.h>

void swap(char *x, char *y)
  __CPROVER_requires(__CPROVER_is_fresh(x, 1) && __CPROVER_is_fresh(y, 1))
    __CPROVER_assigns(*x, *y)
      __CPROVER_ensures(*x == __CPROVER_old(*y) && *y == __CPROVER_old(*x))
{
  char t;
  memcpy(&t, x, 1);
  memcpy(x, y, 1);
  memcpy(y, &t, 1);
}

int main()
{
  char a, b;
  swap(&a, &b);
  return 0;
}
