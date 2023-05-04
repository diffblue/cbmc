#include <stdbool.h>
#include <stdlib.h>

// A function defining an assignable target
void foo_assigns(char *ptr, const size_t size)
{
  __CPROVER_object_upto(ptr, size);

  // an unauthorized side effect that must be detected
  if(ptr && size > 0)
    ptr[0] = 0;
}

// A function defining an freeable target
void foo_frees(char *ptr, const size_t size)
{
  __CPROVER_freeable(ptr);

  // an unauthorized side effect that must be detected
  if(ptr && size > 0)
    ptr[0] = 0;
}

char *foo(char *ptr, const size_t size, const size_t new_size)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(ptr, size))
__CPROVER_assigns(foo_assigns(ptr, size))
__CPROVER_frees(foo_frees(ptr, size))
// clang-format on
{
  if(ptr && new_size > size)
  {
    free(ptr);
    ptr = malloc(new_size);
    return ptr;
  }
  else
  {
    if(size > 0)
    {
      ptr[0] = 0;
    }
    return ptr;
  }
}

int main()
{
  size_t size;
  size_t new_size;
  char *ptr;
  ptr = foo(ptr, size, new_size);
  return 0;
}
