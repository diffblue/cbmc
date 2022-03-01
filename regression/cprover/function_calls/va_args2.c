#include <stdarg.h>

void f(int first, ...)
{
  va_list ap;
  va_start(ap, first);

  int second;
  second = va_arg(ap, int);

  __CPROVER_assert(first == 1, "property 1");
  __CPROVER_assert(second == 2, "property 2");
}

int main()
{
  f(1, 2);
}
