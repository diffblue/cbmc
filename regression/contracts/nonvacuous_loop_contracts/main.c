#include <assert.h>
#include <stdlib.h>

int main()
{
  size_t size;

  char *buf = malloc(size);
  char c;

  size_t start;
  size_t end = start;

  while(end < size)
    // clang-format off
    __CPROVER_loop_invariant(start <= end && end <= size)
    __CPROVER_decreases(size - end)
    // clang-format on
    {
      if(buf[end] != c)
        break;
      end++;
    }

  if(start > size)
  {
    assert(end == start);
  }
  else
  {
    assert(start <= end && end <= size);
  }
}
