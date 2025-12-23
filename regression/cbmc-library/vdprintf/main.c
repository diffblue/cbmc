#include <stdarg.h>
#include <stdio.h>

int xdprintf(int fd, const char *format, ...)
{
  va_list list;
  va_start(list, format);
  int result = vdprintf(fd, format, list);
  va_end(list);
  return result;
}

int main()
{
  xdprintf(1, "%d\n", 42);
  return 0;
}
