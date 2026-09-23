#include <stdarg.h>

int sum(int first, ...)
{
  va_list ap;
  va_start(ap, first);

  int result = first;
  result += va_arg(ap, int);
  result += va_arg(ap, int);
  return result;
}

int main()
{
  int total;
  total = sum(1, 2, 3);
  __CPROVER_assert(total == 1 + 2 + 3, "property 1");
}
