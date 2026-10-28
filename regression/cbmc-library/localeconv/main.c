#include <assert.h>
#include <limits.h>
#include <locale.h>
#include <string.h>

int main(void)
{
  struct lconv *lc = localeconv();
  assert(lc != (void *)0);

  // C11 7.11p2: In the "C" locale, decimal_point is ".".
  assert(lc->decimal_point != (void *)0);
  assert(strcmp(lc->decimal_point, ".") == 0);

  // C11 7.11p2: thousands_sep is "".
  assert(lc->thousands_sep != (void *)0);
  assert(lc->thousands_sep[0] == '\0');

  // C11 7.11p2: frac_digits is CHAR_MAX.
  assert(lc->frac_digits == CHAR_MAX);

  return 0;
}
