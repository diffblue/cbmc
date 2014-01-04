#include <stdlib.h>

int main()
{
  int *p;
  
  p=(int *)malloc(sizeof(int));
  
  *p=1;
  
  assert(*p==1);
  
  free(p);
}
