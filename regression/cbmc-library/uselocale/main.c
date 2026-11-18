#include <assert.h>
#include <locale.h>

int main()
{
  // newlocale has no model; use a distinct non-null handle instead.
  static char dummy;
  locale_t c = (locale_t)&dummy;
  assert(c != LC_GLOBAL_LOCALE);
  assert(uselocale((locale_t)0) == LC_GLOBAL_LOCALE);
  assert(uselocale(c) == LC_GLOBAL_LOCALE);
  assert(uselocale((locale_t)0) == c);
  assert(uselocale(LC_GLOBAL_LOCALE) == c);
  assert(uselocale((locale_t)0) == LC_GLOBAL_LOCALE);
  return 0;
}
