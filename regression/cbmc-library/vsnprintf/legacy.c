#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#ifdef _WIN32
static int format(char *buffer, size_t size, const char *fmt, ...)
{
  va_list list;
  va_start(list, fmt);
  int result = _vsnprintf(buffer, size, fmt, list);
  va_end(list);
  return result;
}
#endif

int main()
{
#ifdef _WIN32
  // Visual Studio's _vsnprintf null-terminates the buffer only if there is
  // room, and returns -1 if the output is longer than the buffer
  char b[4] = {'x', 'x', 'x', 'x'};
  int r = format(b, 4, "%d", 12);
  assert(r == 2 && strcmp(b, "12") == 0);
  r = format(b, 3, "%d", 789);
  assert(r == 3 && b[0] == '7' && b[1] == '8' && b[2] == '9' && b[3] == 'x');
  r = format(b, 2, "%d", 4567);
  assert(r == -1 && b[0] == '4' && b[1] == '5' && b[2] == '9');
  // a size query: _vsnprintf(NULL, 0, ...) returns the length of the output
  r = format(NULL, 0, "%d", 12345);
  assert(r == 5);
#endif
  return 0;
}
