#include <stdarg.h>
int g;

int my_log(int n, ...)
  // clang-format off
  __CPROVER_requires(n == 1)
  __CPROVER_assigns(g)
// clang-format on
{
  va_list ap;
  va_start(ap, n);
  int x = va_arg(ap, int);
  va_end(ap);
  __CPROVER_assert(x == 42, "variadic argument forwarded");
  g = x;
  return 0;
}

int main(void)
{
  my_log(1, 42);
  return 0;
}
