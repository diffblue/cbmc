#define _POSIX_C_SOURCE 200809L

#include <assert.h>
#include <locale.h>
#ifdef __APPLE__
#  include <xlocale.h>
#endif

unsigned long __isoc23_strtoul_l(const char *, char **, int, locale_t);

int main()
{
#ifdef __CPROVER__
  // the model does not read the locale
  locale_t c = (locale_t)0;
#else
  locale_t c = newlocale(LC_ALL_MASK, "C", (locale_t)0);
#endif
  char *end;
  const char *s = "0b101x";
  // C23 7.24.1.7p3: the C23 variant accepts a 0b prefix for base 0 and 2
  assert(__isoc23_strtoul_l(s, &end, 0, c) == 5);
  assert(end == s + 5);
  return 0;
}
