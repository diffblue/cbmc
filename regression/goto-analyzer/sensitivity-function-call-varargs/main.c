#include <stdarg.h>

int bar(int size, ...)
{
  int total = 0;
  va_list args;
  va_start(args, size);
  for(int i = 0; i < size; ++i)
  {
    int val = va_arg(args, int);
    total += val;
  }

  va_end(args);
  return total;
}

int main()
{
  int y = bar(4, 1, 2, 2, 1);
  __CPROVER_assert(y == 6, "assertion y == 6");

  int z = bar(0);
  __CPROVER_assert(z == 0, "assertion z == 0");
}
