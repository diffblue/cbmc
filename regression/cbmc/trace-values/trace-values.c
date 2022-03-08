#include <stdlib.h>

int global_var;

struct S
{
  int f;
  int array[3];
} my_nested[2];

int main()
{
  static int static_var;
  int local_var = 3;
  int *p=&my_nested[0].array[1];
  int *q=&my_nested[1].f;
  int *null=0;
  int *junk;

  global_var=1;
  static_var=2;
  *p=4;
  *q=5;
  *null=6;
  *junk=7;

  // dynamic
  p=malloc(sizeof(int)*2);
  p[1]=8;
  
  // not even a pointer variable
  *(int *)0=9;

  // assign entire struct
  my_nested[1]=my_nested[0];

  // get a trace
  __CPROVER_assert(0, "");
}
