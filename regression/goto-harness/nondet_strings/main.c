#include <assert.h>

void function(char *pointer, int size)
{
  assert(pointer[size - 1] == '\0');
}
