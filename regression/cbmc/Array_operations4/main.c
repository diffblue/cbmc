#include <stdlib.h>

size_t nondet_size_t();
int main()
{
  size_t size = nondet_size_t();
  if(0 < size && size <= __CPROVER_max_malloc_size)
  {
    char *a = malloc(size);
    char *b = malloc(size);
    __CPROVER_array_copy(a, b);
    __CPROVER_assert(__CPROVER_array_equal(a, b), "should pass");
    a[0] = 0;
    __CPROVER_assert(__CPROVER_array_equal(a, b), "may fail");
  }
}
