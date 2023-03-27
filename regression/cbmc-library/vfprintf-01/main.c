#include <stdarg.h>
#include <stdio.h>

int xprintf(const char *format, ...)
{
  va_list list;
  va_start(list, format);
  int result = vfprintf(stdout, format, list);
  va_end(list);
  return result;
}

int main()
{
  xprintf("%d\n", 42);
  return 0;
}
