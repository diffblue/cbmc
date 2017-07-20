#include <stdlib.h>

int main()
{
  unsigned x;

  int *A=malloc(x*sizeof(int));

  char *p=&A[1];

  char c=*p;

  return c;
}
