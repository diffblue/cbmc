
/* FUNCTION: setlocale */

#ifndef __CPROVER_LOCALE_H_INCLUDED
#include <locale.h>
#define __CPROVER_LOCALE_H_INCLUDED
#endif

char *setlocale(int category, const char *locale)
{
  __CPROVER_HIDE:;
  (void)category;
  (void)*locale;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "setlocale_result");
  char *setlocale_result;
  __CPROVER_set_may(setlocale_result, "setlocale_result");
  return setlocale_result;
  #else
  static char setlocale_result[1];
  return setlocale_result;
  #endif
}

/* FUNCTION: localeconv */

#ifndef __CPROVER_LOCALE_H_INCLUDED
#include <locale.h>
#define __CPROVER_LOCALE_H_INCLUDED
#endif

struct lconv *localeconv(void)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "localeconv_result");
  struct lconv *localeconv_result;
  __CPROVER_set_may(localeconv_result, "localeconv_result");
  return localeconv_result;
  #else
  static struct lconv localeconv_result;
  return &localeconv_result;
  #endif
}

/* FUNCTION: uselocale */

// POSIX.1-2024: uselocale sets the current thread's locale to newloc, unless
// it is (locale_t)0, and returns the locale in effect before -- initially
// LC_GLOBAL_LOCALE.  libc++ switches to its "C" locale with it around the
// C library's formatting.

#ifndef _WIN32

#  ifndef __CPROVER_LOCALE_H_INCLUDED
#    include <locale.h>
#    define __CPROVER_LOCALE_H_INCLUDED
#  endif

#  ifdef __APPLE__
#    ifndef __CPROVER_XLOCALE_H_INCLUDED
#      include <xlocale.h>
#      define __CPROVER_XLOCALE_H_INCLUDED
#    endif
#  endif

locale_t uselocale(locale_t newloc)
{
__CPROVER_HIDE:;
  static __CPROVER_thread_local locale_t current = LC_GLOBAL_LOCALE;
  locale_t previous = current;
  if(newloc != (locale_t)0)
    current = newloc;
  return previous;
}

#endif
