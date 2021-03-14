#include <assert.h>
#include <stdlib.h>

int *get_ptr_minus_one(int *ptr)
{
  if(ptr)
    return ptr - 1;
  return 0;
}

int main()
{
  int *begin = malloc(4 * 4);
  int *end = begin + 1;

  if(begin != get_ptr_minus_one(end))
    assert(0);
}
