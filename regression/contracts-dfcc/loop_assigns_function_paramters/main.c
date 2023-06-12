#include <stdlib.h>

void decr(size_t n)
{
  for(; n--;)
    // clang-format off
    __CPROVER_assigns(n)
    __CPROVER_decreases(n)
    // clang-format on
    {
    }
}

int main()
{
  size_t n;
  decr(n);
  return 0;
}
