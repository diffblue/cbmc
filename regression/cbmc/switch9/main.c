#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));

  if(!p)
    return 1;

  switch(*p)
  {
  case 1:
  case 2:
  case 3:
    return 0;
  case 4:
  default:
    return -1;
  }
}
