#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  char *end;
  const char *s;

  // C23 7.24.1.7p5: '-' negates the converted value in the return type
  assert(strtoull("-1", 0, 10) == ULLONG_MAX);

  errno = 0;
  assert(strtoull("18446744073709551615", 0, 10) == ULLONG_MAX);
  assert(errno == 0);
  assert(strtoull("-18446744073709551616", 0, 10) == ULLONG_MAX);
  assert(errno == ERANGE);

  // endptr points past the subject sequence also after a range error
  errno = 0;
  s = "99999999999999999999x";
  assert(strtoull(s, &end, 10) == ULLONG_MAX);
  assert(errno == ERANGE);
  assert(end == s + 20);

  // 64 binary digits
  assert(
    strtoull(
      "1111111111111111111111111111111111111111111111111111111111111111",
      0,
      2) == ULLONG_MAX);

  return 0;
}
