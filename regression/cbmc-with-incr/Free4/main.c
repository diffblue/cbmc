#include <stdlib.h>

void my_free(int *q)
{
  free(q);
}

int main()
{
  int *p=malloc(sizeof(int));
  
  *p=2;
  
  my_free(p);

  // should fail  
  *p=3;
}
