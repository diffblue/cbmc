#include <assert.h>
#include <stdarg.h>
#include <stdio.h>

int xscanf(const char *format, ...)
{
  va_list list;
  va_start(list, format);
  int result = vscanf(format, list);
  va_end(list);
  return result;
}

int main()
{
  char dest[10];
  int result = xscanf("%s", dest);
  assert(result == 1);
  return 0;
}
