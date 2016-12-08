#include <stdlib.h>

int *array;

int main()
{
  unsigned size;
  __CPROVER_assume(size==1);

  // produce unbounded array that does not have byte granularity
  array=malloc(size*sizeof(int));
  array[0]=0x01020304;

  int array0=array[0];
  __CPROVER_assert(array0==0x01020304, "array[0] matches");

  char *p=(char *)array;
  char p0=p[0];
  char p1=p[1];
  char p2=p[2];
  char p3=p[3];
  __CPROVER_assert(p0==1, "p[0] matches");
  __CPROVER_assert(p1==2, "p[1] matches");
  __CPROVER_assert(p2==3, "p[2] matches");
  __CPROVER_assert(p3==4, "p[3] matches");

  unsigned short *q=(unsigned short *)array;
  unsigned short q0=q[0];
  __CPROVER_assert(q0==0x0102, "p[0,1] matches");
}
