// declare strtol_l as <stdlib.h> does for C programs that use it, which glibc
// 2.38 and later redirect to __isoc23_strtol_l
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
  assert(strtol_l("998", 0, 10, c) == 998l);
  assert(strtol_l("ff", &end, 16, c) == 255l);
  assert(strtol_l("2147483647", 0, 10, c) == 2147483647l);
  assert(strtol_l("12x", &end, 10, c) == 12l);
  assert(*end == 'x');
  // fails: the result is 12
  assert(strtol_l("12x", &end, 10, c) == 13l);
  return 0;
}
