#include <assert.h>
#include <stdlib.h>

int main()
{
  int *ptr = malloc(sizeof(int));
  *ptr = 42;
  ptr = realloc(ptr, 20);
  assert(*ptr == 42);

  int *ptr2 = malloc(2 * sizeof(int));
  *ptr2 = 42;
  *(ptr2 + 1) = 42;
  ptr2 = realloc(ptr2, 20);
  assert(*ptr2 == 42);
  assert(*(ptr2 + 1) == 42);

  return 0;
}
