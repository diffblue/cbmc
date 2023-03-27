#include <assert.h>
#ifndef _WIN32
#  include <unistd.h>
#else
int _usleep(unsigned);
#endif

int main()
{
  unsigned input;
  int retval = _usleep(input);
  assert(retval == 0 || retval == -1);
  return 0;
}
