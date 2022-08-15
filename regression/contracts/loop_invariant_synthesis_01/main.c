#include <stdlib.h>

int main()
{
  unsigned int size;
  __CPROVER_assume(size < 50);
  int *p = malloc(size * 4);
  int result = 0;

  for(unsigned int i = 0; i < size; i++)
  {
    result += p[i];
  }

  for(unsigned int i = 0; i < size; i++)
    // clang-format off
  __CPROVER_loop_invariant(1 == 1)
    // clang-format on
    {
      result += p[i];
    }

  for(unsigned int i = 0; i < size; i++)
  {
    result += p[i];
  }
}
