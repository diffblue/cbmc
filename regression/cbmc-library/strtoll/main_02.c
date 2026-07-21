#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  char *end;
  const char *s;

  // digits must be valid for the base
  assert(strtoll("102", &end, 2) == 2);
  assert(*end == '2');
  assert(strtoll("09", 0, 0) == 0);

  // leading white space and '+'
  assert(strtoll(" \t+12", 0, 10) == 12);

  // no conversion: endptr is nptr
  s = "  +x";
  assert(strtoll(s, &end, 10) == 0);
  assert(end == s);

  // an incomplete hex prefix is not part of the subject sequence
  s = "0x";
  assert(strtoll(s, &end, 16) == 0);
  assert(end == s + 1);
  s = "0xg";
  assert(strtoll(s, &end, 0) == 0);
  assert(end == s + 1);

  // the C23 0b prefix is not accepted by the pre-C23 function
  s = "0b101";
  assert(strtoll(s, &end, 0) == 0);
  assert(end == s + 1);

  // the extreme values are representable
  errno = 0;
  assert(strtoll("-9223372036854775808", 0, 10) == LLONG_MIN);
  assert(errno == 0);
  assert(strtoll("9223372036854775807", 0, 10) == LLONG_MAX);
  assert(errno == 0);

  // one past them is not
  assert(strtoll("-9223372036854775809", 0, 10) == LLONG_MIN);
  assert(errno == ERANGE);
  errno = 0;
  s = "9223372036854775808x";
  assert(strtoll(s, &end, 10) == LLONG_MAX);
  assert(errno == ERANGE);
  // endptr points past the subject sequence also after a range error
  assert(end == s + 19);

  // invalid base
  errno = 0;
  assert(strtoll("1", 0, 37) == 0);
  assert(errno == EINVAL);

  // more than 31 characters
  assert(strtoll("                              12", 0, 10) == 12);
  assert(
    strtoll("1111111111111111111111111111111111111111", 0, 2) ==
    0xFFFFFFFFFFll);

  return 0;
}
