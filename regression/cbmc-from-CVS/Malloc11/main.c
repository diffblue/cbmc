#include <stdlib.h>

int main()
{
  int n;
  int x;
  int *a;
  _Bool nondet;

  __CPROVER_assume (n <= 10);

  if (n <= 0)
  {
    if(nondet)
      a = NULL;
    else
    {
      a = & x;
      n=1;
    }
  }
  else
    a = (int *) malloc(n * sizeof (int));

  if( a != NULL)
    a[0]=0;
    
  if(n>=1) assert(a[0]==0);

  return 1;
}
