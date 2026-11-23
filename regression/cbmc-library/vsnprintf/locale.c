#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#if defined(__APPLE__) || defined(__FreeBSD__)
#  include <xlocale.h>

static int format(char *buffer, size_t size, const char *fmt, ...)
{
  va_list list;
  va_start(list, fmt);
  int result = vsnprintf_l(buffer, size, NULL, fmt, list);
  va_end(list);
  return result;
}
#endif

int main()
{
#if defined(__APPLE__) || defined(__FreeBSD__)
  // snprintf_l and vsnprintf_l (macOS, FreeBSD) take a locale, which the
  // integer conversions do not depend on
  char b[8];
  int r = snprintf_l(b, sizeof b, NULL, "%d|%x", 42, 255);
  assert(r == 5 && strcmp(b, "42|ff") == 0);
  r = format(b, 4, "%05d", 7);
  assert(r == 5 && strcmp(b, "000") == 0);
#endif
  return 0;
}
