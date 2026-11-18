// declare strtoul_l as <stdlib.h> does for C programs that use it, which glibc
// 2.38 and later redirect to __isoc23_strtoul_l
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
  assert(strtoul_l("998", 0, 10, c) == 998ul);
  assert(strtoul_l("ff", &end, 16, c) == 255ul);
  assert(strtoul_l("4294967295", 0, 10, c) == 4294967295ul);
  assert(strtoul_l("12x", &end, 10, c) == 12ul);
  assert(*end == 'x');
  // fails: the result is 12
  assert(strtoul_l("12x", &end, 10, c) == 13ul);
  return 0;
}
