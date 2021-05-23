#include <assert.h>
#include <stdlib.h>

int main()
{
  int *p1 = malloc(sizeof(int));

  assert(p1 < p1 + 1);
}
