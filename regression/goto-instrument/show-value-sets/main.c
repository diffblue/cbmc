#include <stdlib.h>

#define BIG 4096

int main()
{
  // Uninitialized pointer
  int *u;

  // Basic assignment
  u = NULL;
  int a;
  u = &a;

  // Test merging and the loss of correlation
  int *p;
  int *q;
  int b;
  int c;
  int nondet;
  if(nondet)
  {
    p = &b;
    q = &c;
  }
  else
  {
    p = &c;
    q = &b;
  }

  // Test widening
  int array[BIG];
  int *s = &(array[0]);
  for(int i = 0; i < BIG; ++i)
  {
    s = &array[i];
  }

  return 0;
}
