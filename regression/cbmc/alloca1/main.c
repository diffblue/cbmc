#include <stdlib.h>

int main()
{
  int *p = alloca(sizeof(int));
  *p = 42;
  free(p);
}
