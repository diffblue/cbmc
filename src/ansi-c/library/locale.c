
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

#ifndef __CPROVER_LIMITS_H_INCLUDED
#  include <limits.h>
#  define __CPROVER_LIMITS_H_INCLUDED
#endif

#ifndef __CPROVER_STDDEF_H_INCLUDED
#  include <stddef.h>
#  define __CPROVER_STDDEF_H_INCLUDED
#endif

// C23 7.11.2.1: the members of the structure for the "C" locale are "."
// for decimal_point, the empty string for the other strings, and CHAR_MAX
// (not available) for the char members.  No setlocale call is modelled to
// change the locale.
#if defined(_MSC_VER)
// the Universal CRT's wide-character copies of the strings
static void __CPROVER_localeconv_platform_members(struct lconv *result)
{
  static wchar_t w_decimal_point[] = L".";
  static wchar_t w_empty[] = L"";
  result->_W_decimal_point = w_decimal_point;
  result->_W_thousands_sep = w_empty;
  result->_W_int_curr_symbol = w_empty;
  result->_W_currency_symbol = w_empty;
  result->_W_mon_decimal_point = w_empty;
  result->_W_mon_thousands_sep = w_empty;
  result->_W_positive_sign = w_empty;
  result->_W_negative_sign = w_empty;
}
#elif !defined(_WIN32)
// the members C99 added (Windows' C libraries do not have them)
static void __CPROVER_localeconv_platform_members(struct lconv *result)
{
  result->int_p_cs_precedes = CHAR_MAX;
  result->int_n_cs_precedes = CHAR_MAX;
  result->int_p_sep_by_space = CHAR_MAX;
  result->int_n_sep_by_space = CHAR_MAX;
  result->int_p_sign_posn = CHAR_MAX;
  result->int_n_sign_posn = CHAR_MAX;
}
#else
static void __CPROVER_localeconv_platform_members(struct lconv *result)
{
  (void)result;
}
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
  static struct lconv result;
  static char decimal_point[] = ".";
  static char empty[] = "";
  result.decimal_point = decimal_point;
  result.thousands_sep = empty;
  result.grouping = empty;
  result.int_curr_symbol = empty;
  result.currency_symbol = empty;
  result.mon_decimal_point = empty;
  result.mon_thousands_sep = empty;
  result.mon_grouping = empty;
  result.positive_sign = empty;
  result.negative_sign = empty;
  result.int_frac_digits = CHAR_MAX;
  result.frac_digits = CHAR_MAX;
  result.p_cs_precedes = CHAR_MAX;
  result.p_sep_by_space = CHAR_MAX;
  result.n_cs_precedes = CHAR_MAX;
  result.n_sep_by_space = CHAR_MAX;
  result.p_sign_posn = CHAR_MAX;
  result.n_sign_posn = CHAR_MAX;
  __CPROVER_localeconv_platform_members(&result);
  return &result;
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
