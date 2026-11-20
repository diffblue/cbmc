#include <assert.h>
#include <string.h>
#include <time.h>

int main(void)
{
  struct tm t;
  t.tm_sec = 0;
  t.tm_min = 0;
  t.tm_hour = 0;
  t.tm_mday = 1;
  t.tm_mon = 0;
  t.tm_year = 100;
  t.tm_wday = 6;
  t.tm_yday = 0;
  t.tm_isdst = 0;

  char *s = asctime(&t);
  // C11 7.27.3.1: result is a 26-byte NUL-terminated string.
  assert(strlen(s) <= 25);
  return 0;
}
