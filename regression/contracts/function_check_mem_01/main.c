// function_check_mem_01

// This test checks the use of pointer-related predicates in assumptions and
// requires.
// This test currently fails because of the lack of support for assuming
// pointer predicates.

#include <stddef.h>

#define __CPROVER_VALID_MEM(ptr, size)                                         \
  __CPROVER_POINTER_OBJECT((ptr)) != __CPROVER_POINTER_OBJECT(NULL) &&         \
    !__CPROVER_is_invalid_pointer((ptr)) &&                                    \
    __CPROVER_POINTER_OBJECT((ptr)) !=                                         \
      __CPROVER_POINTER_OBJECT(__CPROVER_deallocated) &&                       \
    __CPROVER_POINTER_OBJECT((ptr)) !=                                         \
      __CPROVER_POINTER_OBJECT(__CPROVER_dead_object) &&                       \
    (__builtin_object_size((ptr), 1) >= (size) &&                              \
     __CPROVER_POINTER_OFFSET((ptr)) >= 0l)

typedef struct bar
{
  int x;
  int y;
  int z;
} bar;

void foo(bar *x)
  __CPROVER_requires(__CPROVER_VALID_MEM(x, sizeof(bar)))
{
  x->x += 1;
  return;
}

int main()
{
  bar *y;
  __CPROVER_assume(__CPROVER_VALID_MEM(y, sizeof(bar)));
  y->x = 0;
  return 0;
}
