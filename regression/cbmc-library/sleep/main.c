#include <assert.h>
#ifndef _WIN32
#  include <unistd.h>
#else
unsigned sleep(unsigned);
#endif

int main()
{
  assert(sleep(42) <= 42);
  return 0;
}
