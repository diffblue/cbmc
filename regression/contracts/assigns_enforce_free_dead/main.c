#include <assert.h>
#include <stdlib.h>

int foo(int *x, int **p) __CPROVER_assigns(*x; p : *p; p && *p : **p)
{
  if(p && *p)
    **p = 0;

  {
    int y;
    y = 1;
    *x = 0;

    if(nondet_bool())
      return 0;

    if(p)
      *p = &y;

    // y goes DEAD here, unconditionally
  }

  if(p && *p)
    **p = 0;

  int a = 1;

  if(x == NULL)
  {
    return 1;
    // a goes DEAD here, conditionally
  }

  int *z = malloc(100 * sizeof(int));
  int *w = NULL;

  if(z)
  {
    w = &(z[10]);
    *w = 0;

    int *q = &(z[20]);
    *q = 1;
    // q goes DEAD here, unconditionally
  }

  free(z); // should not fail because free(NULL) is allowed in C

  z = malloc(sizeof(int));
  if(nondet_bool())
  {
    free(z); // should not fail because free(NULL) is allowed in C
    // here z is deallocated, conditionally
  }

  *x = 1;
  x = 0;
}

int main()
{
  int z;
  int *x = malloc(sizeof(int));
  foo(&z, &x);
}
