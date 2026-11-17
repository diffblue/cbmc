#include <assert.h>
#include <locale.h>

int main()
{
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
  if(c == (locale_t)0)
    return 0;
  assert(uselocale((locale_t)0) == LC_GLOBAL_LOCALE);
  assert(uselocale(c) == LC_GLOBAL_LOCALE);
  assert(uselocale((locale_t)0) == c);
  assert(uselocale(LC_GLOBAL_LOCALE) == c);
  assert(uselocale((locale_t)0) == c);
  return 0;
}
