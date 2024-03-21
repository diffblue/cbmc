#include <assert.h>
#include <stdarg.h>
#include <stdio.h>

int vasprintf(char **ptr, const char *fmt, va_list ap);

int xasprintf(char **ptr, const char *format, ...)
{
  va_list list;
  va_start(list, format);
  int result = vasprintf(ptr, format, list);
  va_end(list);
  return result;
}

int main()
{
  char *result = NULL;
  int bytes = xasprintf(&result, "%d\n", 42);
  if(bytes != -1)
  {
    assert(result[bytes] == 0);
    free(result);
  }
  return 0;
}
