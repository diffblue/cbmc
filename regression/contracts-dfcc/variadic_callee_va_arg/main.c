#include <stdarg.h>

int g;

int my_log(const char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  int x = va_arg(ap, int);
  va_end(ap);
  g = x;
  return x;
}

void callee(int v)
  // clang-format off
  __CPROVER_requires(1)
  __CPROVER_assigns(g)
// clang-format on
{
  int r = my_log("%d", v);
  __CPROVER_assert(r == v, "variadic argument received");
}

int main(void)
{
  int v;
  callee(v);
  return 0;
}
