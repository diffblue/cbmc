#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  free(p); // safe
  free(p); // unsafe
}
