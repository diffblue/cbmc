// C17 7.16.1.1, N5008 [cstdarg.syn]: va_arg (GCC's and Clang's
// __builtin_va_arg) reads the next variadic argument.  The C++ parser
// rejected it.
#include <cstdarg>
extern "C" void __CPROVER_assert(bool, const char *);
int sum(int count, ...)
{
  va_list ap;
  va_start(ap, count);
  int total = 0;
  for(int i = 0; i < count; ++i)
    total += va_arg(ap, int);
  va_end(ap);
  return total;
}
double second(int n, ...)
{
  va_list ap;
  va_start(ap, n);
  va_arg(ap, int);
  double d = va_arg(ap, double);
  va_end(ap);
  return d;
}
int main()
{
  __CPROVER_assert(sum(3, 1, 2, 4) == 7, "three ints");
  __CPROVER_assert(second(0, 1, 2.5) == 2.5, "an int, then a double");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
