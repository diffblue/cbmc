#include <assert.h>
#include <time.h>

int main(void)
{
  time_t t = 0;
  struct tm *p = localtime(&t);
  // C11 7.27.3.4: localtime may return NULL.
  assert(p != 0);
  return 0;
}
