#include <stdarg.h>
#include <stddef.h>

static int fmt(char *str, size_t size, size_t bufsize, const char *f, ...)
{
  va_list list;
  va_start(list, f);
  int r = __builtin___vsnprintf_chk(str, size, 0, bufsize, f, list);
  va_end(list);
  return r;
}

int main()
{
  char b[4];
  // the object size is unknown
  fmt(b, sizeof b, (size_t)-1, "%d", 1);
  // size exceeds the object size
  fmt(b, 8, sizeof b, "%d", 1);
  return 0;
}
