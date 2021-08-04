#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  (*p)++;

  return 0;
}
