#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  if(CHAR_BIT * sizeof(long) <= 64)
  {
    char *a[] = {"0x7fffffffffffffffF", "-0x7fffffffffffffffF"};

    errno = 0;
    assert(strtol(a[0], 0, 16) == LONG_MAX);
    assert(errno == ERANGE);

    errno = 0;
    assert(strtol(a[1], 0, 16) == LONG_MIN);
    assert(errno == ERANGE);
  }

  return 0;
}
