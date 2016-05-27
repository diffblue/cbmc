#include <stdlib.h>

int *array;

int main()
{
  unsigned size;
  __CPROVER_assume(size==1);

  array=malloc(size*sizeof(int)); // produce unbounded array
  array[0]=0x01020304;

  int array0=array[0];
  __CPROVER_assert(array0==0x01020304, "array[0] matches");

  char *p=(char *)array;
  char p0=p[0];
  __CPROVER_assert(p0==1, "p[0] matches");
  
  unsigned short *q=(unsigned short *)array;
  unsigned short q0=q[0];
  __CPROVER_assert(q0==0x0102, "p[0,1] matches");
}
