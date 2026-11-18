#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  char *end;
  const char *s = "0x";

  // an incomplete hex prefix is not part of the subject sequence
  assert(strtoul(s, &end, 16) == 0);
  assert(end == s + 1);

  if(sizeof(unsigned long) == 8)
  {
    errno = 0;
    assert(strtoul("18446744073709551616", 0, 10) == ULONG_MAX);
    assert(errno == ERANGE);
  }
  else
  {
    errno = 0;
    assert(strtoul("4294967296", 0, 10) == ULONG_MAX);
    assert(errno == ERANGE);
  }

  return 0;
}
