#include <assert.h>
#include <stdarg.h>
#include <stdio.h>

int xsnprintf(char *ptr, size_t size, const char *format, ...)
{
  va_list list;
  va_start(list, format);
  int result = vsnprintf(ptr, size, format, list);
  va_end(list);
  return result;
}

int main()
{
  char result[10];
  int bytes = xsnprintf(result, 10, "%d\n", 42);
  assert(bytes <= 10);
  return 0;
}
