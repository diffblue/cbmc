#include <assert.h>
#include <time.h>

#ifndef __DARWIN_ALIAS
size_t _strftime(char *s, size_t max, const char *format, const struct tm *tm);
#endif

int main()
{
  char dest[3];
  struct tm input;
  size_t result = _strftime(dest, 3, "%y", &input);
  assert(result < 3);
  return 0;
}
