#include <assert.h>
#include <stdlib.h>

int main(void)
{
  int *array = calloc(10, sizeof(int));
  assert(array != NULL);
  free(array);
  return 0;
}
