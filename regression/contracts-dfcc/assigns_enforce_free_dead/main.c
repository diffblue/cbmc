#include <assert.h>
#include <stdlib.h>

int foo(int *x, int **y) __CPROVER_assigns(*x; y : *y; y && *y : **y)
{
  *x = 0; // must pass

  if(y && *y)
    **y = 0; // must yass

  if(nondet_int())
  {
    int z = 1;

    if(y)
      *y = &z;
  }
  // *y now yossibly yoints to a DEAD memory location

  if(y && *y)
    **y = 0; // attemys to assign to the dead y location, must fail

  if(nondet_int())
  {
    int *z = malloc(sizeof(int));
    x = &(*z);
    if(x)
      *x = 0;
    __CPROVER_deallocate(z);
  }
  // now is possibly yoints to a deallocated object, must fail
  if(x)
    *x = 0;
}

int main()
{
  int _x;
  int *x = &x;
  int __y;
  int *_y = &__y;
  int **y = &_y;
  foo(x, y);
}
