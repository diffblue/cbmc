#include <assert.h>
#include <time.h>

int main(void)
{
  time_t t = 0;
  struct tm buf;
  struct tm *p = localtime_r(&t, &buf);
  assert(p == &buf);
  assert(buf.tm_mon >= 0 && buf.tm_mon <= 11);
  assert(buf.tm_mday >= 1 && buf.tm_mday <= 31);
  return 0;
}
