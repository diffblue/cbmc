// declare strtoull_l as <stdlib.h> does for C programs that use it, which glibc
// 2.38 and later redirect to __isoc23_strtoull_l
#define _GNU_SOURCE

#include <assert.h>
#include <locale.h>
#include <stdlib.h>
#ifdef __APPLE__
#  include <xlocale.h>
#endif

int main()
{
#ifdef __CPROVER__
  // the model does not read the locale
  locale_t c = (locale_t)0;
#else
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
#endif
  char *end;
  assert(strtoull_l("998", 0, 10, c) == 998ull);
  assert(strtoull_l("ff", &end, 16, c) == 255ull);
  assert(
    strtoull_l("18446744073709551615", 0, 10, c) == 18446744073709551615ull);
  assert(strtoull_l("12x", &end, 10, c) == 12ull);
  assert(*end == 'x');
  // fails: the result is 12
  assert(strtoull_l("12x", &end, 10, c) == 13ull);
  return 0;
}
