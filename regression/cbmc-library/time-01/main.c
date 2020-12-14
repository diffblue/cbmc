#include <assert.h>
#include <time.h>

int main()
{
  time_t t1 = time(0);

  time_t t;
  time_t t2 = time(&t);
  assert(t2 == t);

  return 0;
}
