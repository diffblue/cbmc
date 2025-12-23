#include <assert.h>
#ifndef _WIN32
#  include <unistd.h>
#else
unsigned _sleep(unsigned);
#endif

int main()
{
  assert(_sleep(42) <= 42);
  return 0;
}
