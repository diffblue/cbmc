#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

int format(char *buffer, size_t size, const char *fmt, ...)
{
  va_list list;
  va_start(list, fmt);
  int result = vsnprintf(buffer, size, fmt, list);
  va_end(list);
  return result;
}

int main()
{
  char b[24];
  int r = format(b, sizeof b, "%d|%5x|%-3s|%c%%", -42, 255u, "ab", 'z');
  assert(r == 16 && strcmp(b, "-42|   ff|ab |z%") == 0);
  r = format(b, sizeof b, "%+.3d %#o %#X %lld", 7, 8, 255, -1234567890123ll);
  assert(r == 28 && strcmp(b, "+007 010 0XFF -12345678") == 0);
  r = format(b, 4, "%u", 123456u);
  assert(r == 6 && strcmp(b, "123") == 0);
  // %f is not modelled exactly: what precedes it is
  r = format(b, sizeof b, "x%fy", 1.5);
  assert(r >= 1 && b[0] == 'x');
  unsigned x;
  __CPROVER_assume(x < 1000);
  r = format(b, sizeof b, "%u", x);
  assert(r >= 1 && r <= 3 && b[r] == 0);
  assert(r == 3);
  return 0;
}
