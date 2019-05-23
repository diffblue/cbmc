#include <stdlib.h>

int main()
{
  int *ptr = malloc(sizeof(int) * 2);
  int *other_ptr;
  if(ptr + 1 == other_ptr)
    return 0;
  __CPROVER_assert(0, "");
}
