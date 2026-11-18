#include <assert.h>
#include <locale.h>

#ifdef __GLIBC__

// libstdc++ declares this in bits/c++locale.h
locale_t __uselocale(locale_t);

int main()
{
  static char dummy;
  locale_t c = (locale_t)&dummy;
  assert(__uselocale(c) == LC_GLOBAL_LOCALE);
  // __uselocale and uselocale share the same state
  assert(uselocale((locale_t)0) == c);
  return 0;
}

#else

int main()
{
  return 0;
}

#endif
