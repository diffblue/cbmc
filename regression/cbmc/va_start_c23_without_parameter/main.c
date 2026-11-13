// C23 7.16.1.4: va_start(ap, ...) ignores any argument after ap; GCC's
// <stdarg.h> expands it to __builtin_va_start(ap, 0).  The variadic
// arguments follow the last named parameter -- also when the second
// argument is an object that is not that parameter (undefined before C23,
// GCC warns and starts after the last named parameter).
#include <assert.h>
#include <stdarg.h>

int sum(int n, ...)
{
  va_list ap;
  __builtin_va_start(ap, 0);
  int s = 0;
  for(int i = 0; i < n; ++i)
    s += va_arg(ap, int);
  va_end(ap);
  return s;
}

int not_a_parameter(int n, ...)
{
  int x = 0;
  va_list ap;
  va_start(ap, x);
  int r = va_arg(ap, int);
  va_end(ap);
  return r;
}

int main()
{
  assert(sum(3, 1, 2, 4) == 7);
  assert(not_a_parameter(1, 9) == 9);
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
