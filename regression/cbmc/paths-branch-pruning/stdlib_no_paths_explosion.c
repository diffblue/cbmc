#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));
  int *r = malloc(sizeof(int));
  if(p && q && r)
  {
    *p = 1;
    *q = 2;
    *r = 3;
    free(p);
    free(q);
    free(r);
  }
  return 0;
}
