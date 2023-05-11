#include <stdlib.h>

#define SIZE 32
int foo() __CPROVER_assigns()
{
  char buf1[SIZE];
  char buf2[SIZE];
  char buf3[SIZE];
  size_t i = 0;
  while(i < SIZE)
    // clang-format off
    __CPROVER_assigns(
      i,
      __CPROVER_object_whole(buf1),
      __CPROVER_object_from(&buf2[10]),
      *&buf3[10])
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      buf1[i] = 0;        // pass
      buf1[SIZE - 1] = 0; // pass

      buf2[0] = 0;        // fail
      buf2[10] = 0;       // pass
      buf2[11] = 0;       // pass
      buf1[SIZE - 1] = 0; // pass

      buf3[0] = 0;        // fail
      buf3[9] = 0;        // fail
      buf3[10] = 0;       // pass
      buf3[11] = 0;       // fail
      buf3[SIZE - 1] = 0; // fail
      i++;
    }
}

void main()
{
  foo();
}
