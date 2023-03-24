#include <stdlib.h>

#define SIZE 8

void main()
{
  int b[SIZE];
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      b[i] = 1;
    }
}
