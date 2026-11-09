#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  int x = *p; // safe
  free(p);
  int y = *p; // unsafe
}
