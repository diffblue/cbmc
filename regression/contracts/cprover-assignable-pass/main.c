#include <stdlib.h>

__CPROVER_assignable_t my_write_set(char *arr, size_t size)
{
  __CPROVER_assert(
    !arr || __CPROVER_rw_ok(arr, size), "target null or writable");

  if(arr && size > 0)
  {
    __CPROVER_whole_object(arr);
    __CPROVER_object_upto(arr, size);
    __CPROVER_object_from(arr);
    __CPROVER_typed_target(arr[0]);
  }
}

void main()
{
  int nondet;
  size_t size;
  char *arr;
  arr = nondet ? malloc(size) : NULL;
  // pointer is not invalid
  my_write_set(arr, size);
}
