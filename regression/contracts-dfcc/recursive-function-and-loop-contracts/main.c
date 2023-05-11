#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

bool nondet_bool();

int foo(char *arr, const size_t size, size_t offset)
  // clang-format off
__CPROVER_requires( 0 < size && offset <= size  && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(__CPROVER_object_whole(arr))
// clang-format on
{
  if(offset == 0)
    return 0;

  // recursive call
  foo(arr, size, offset - 1);

  size_t i1 = offset;
  while(i1 < size)
    // clang-format off
    __CPROVER_assigns(i1, __CPROVER_object_whole(arr))
    __CPROVER_loop_invariant(i1 <= size)
    __CPROVER_decreases(size - i1)
    // clang-format on
    {
      static int local_static = 0;
      local_static = 1;
      arr[i1] = 1;
      size_t i2 = offset;
      while(i2 < size)
        //clang-format off
        __CPROVER_assigns(i2, __CPROVER_object_whole(arr))
          __CPROVER_loop_invariant(i2 <= size) __CPROVER_decreases(size - i2)
        //clang-format on
        {
          local_static = 2;
          arr[i2] = 2;
          i2++;
        }
      bool must_break = nondet_bool();
      if(must_break)
      {
        size_t i3 = offset;
        while(i3 < size)
          // clang-format off
          __CPROVER_assigns(i3, __CPROVER_object_whole(arr))
          __CPROVER_loop_invariant(i3 <= size)
          __CPROVER_decreases(size - i3)
          // clang-format on
          {
            local_static = 3;
            arr[i3] = 3;
            i3++;
          }
        break;
      }
      i1++;
    }
}

int main()
{
  char *arr;
  size_t size;
  size_t offset;
  foo(arr, size, offset);
}
