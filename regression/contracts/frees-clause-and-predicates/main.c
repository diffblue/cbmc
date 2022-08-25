#include <stdbool.h>
#include <stdlib.h>

// A function defining an assignable target
__CPROVER_assignable_t foo_assigns(char *arr, const size_t size)
{
  __CPROVER_object_upto(arr, size);
}

// A function defining an freeable target
__CPROVER_freeable_t foo_frees(char *arr, const size_t size)
{
  __CPROVER_freeable(arr);
}

bool is_freeable(void *ptr)
{
  bool is_dynamic_object = (ptr == 0) | __CPROVER_DYNAMIC_OBJECT(ptr);
  bool has_offset_zero = (ptr == 0) | (__CPROVER_POINTER_OFFSET(ptr) == 0);
  return is_dynamic_object & has_offset_zero;
}

char *foo(char *ptr, const size_t size, const size_t new_size)
  // clang-format off
__CPROVER_requires(__CPROVER_is_freeable(ptr))
__CPROVER_assigns(foo_assigns(ptr, size))
__CPROVER_frees(foo_frees(ptr, size))
__CPROVER_ensures(
  (ptr && new_size > size) ==>
    __CPROVER_is_fresh(__CPROVER_return_value, new_size))
__CPROVER_ensures(
  (ptr && new_size > size) ==>
    __CPROVER_is_freed(ptr))
__CPROVER_ensures(
    !(ptr && new_size > size) ==>
      __CPROVER_return_value == __CPROVER_old(ptr))
// clang-format on
{
  // The harness  allows to add a nondet offset to the pointer passed to foo.
  // Proving this assertion shows that the __CPROVER_is_freeable(ptr) assumption
  // is in effect as expected for the verification
  __CPROVER_assert(is_freeable(ptr), "ptr is freeable");

  if(ptr && new_size > size)
  {
    free(ptr);
    ptr = malloc(new_size);

    // write at some nondet i (should be always allowed since ptr is fresh)
    size_t i;
    if(i < new_size)
      ptr[i] = 0;

    return ptr;
  }
  else
  {
    // write at some nondet i
    size_t i;
    if(i < size)
      ptr[i] = 0;

    return ptr;
  }
}

int main()
{
  size_t size;
  size_t new_size;
  __CPROVER_assume(size < __CPROVER_max_malloc_size);
  __CPROVER_assume(new_size < __CPROVER_max_malloc_size);
  char *arr = malloc(size);
  arr = foo(arr, size, new_size);
  return 0;
}
