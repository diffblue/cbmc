#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  char *end;
  const char *s = "  -x";

  // no conversion: endptr is nptr
  assert(strtol(s, &end, 10) == 0);
  assert(end == s);

  // digits must be valid for the base
  assert(strtol("102", 0, 2) == 2);
  assert(strtol("09", 0, 0) == 0);

  // LONG_MIN is representable
  if(sizeof(long) == 8)
  {
    errno = 0;
    assert(strtol("-9223372036854775808", 0, 10) == LONG_MIN);
    assert(errno == 0);
  }
  else
  {
    errno = 0;
    assert(strtol("-2147483648", 0, 10) == LONG_MIN);
    assert(errno == 0);
  }

  return 0;
}
