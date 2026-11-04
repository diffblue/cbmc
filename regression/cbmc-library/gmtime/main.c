#include <assert.h>
#include <time.h>

int main(void)
{
  time_t t = 4102444800; // 2100-01-01 00:00:00 UTC
  struct tm *p = gmtime(&t);
  // C11 7.27.3.3: gmtime may return NULL.
  // Assert it always succeeds: must FAIL.
  assert(p != 0);
  return 0;
}
