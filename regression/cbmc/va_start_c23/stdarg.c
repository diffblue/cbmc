#include <stdarg.h>

int first(char c, ...)
{
  va_list ap;
  va_start(ap, c);
  int x = va_arg(ap, int);
  va_end(ap);
  return x;
}

int main()
{
  __CPROVER_assert(first('a', 42) == 42, "first");
  return 0;
}
