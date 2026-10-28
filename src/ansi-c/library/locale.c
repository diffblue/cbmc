
/* FUNCTION: setlocale */

#ifndef __CPROVER_LOCALE_H_INCLUDED
#include <locale.h>
#define __CPROVER_LOCALE_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);

__CPROVER_bool __CPROVER_locale_may_have_changed;

char *setlocale(int category, const char *locale)
{
  __CPROVER_HIDE:;
  (void)category;
  // C11 7.11.1.1p7: "A null pointer for locale causes the setlocale
  // function to return a pointer to the string associated with the
  // category for the program's current locale."
  if(locale != 0)
    (void)*locale;
#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "setlocale_result");
  char *setlocale_result;
  __CPROVER_set_may(setlocale_result, "setlocale_result");
  return setlocale_result;
  #else
  // C11 7.11.1.1p6: "If the selection cannot be honored, the
  // setlocale function returns a null pointer."
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
    return (char *)0;
  if(locale != 0)
    __CPROVER_locale_may_have_changed = 1;
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

char __VERIFIER_nondet_char(void);

#ifndef LIBRARY_CHECK
__CPROVER_bool __CPROVER_locale_may_have_changed;
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
  // C11 7.11.2.1: localeconv never returns a null pointer. C11 7.11.1.1p4:
  // at program startup, the "C" locale is in effect, with the values given in
  // C11 7.11p2. Once setlocale has been called, any locale may be in effect.
  static struct lconv localeconv_result;
  __CPROVER_bool c_locale = !__CPROVER_locale_may_have_changed;

#  define __CPROVER_LCONV_STRING(member, c_value)                              \
    do                                                                         \
    {                                                                          \
      static char member##_buffer[8];                                          \
      if(c_locale)                                                             \
      {                                                                        \
        member##_buffer[0] = c_value;                                          \
        member##_buffer[1] = 0;                                                \
      }                                                                        \
      else                                                                     \
      {                                                                        \
        __CPROVER_havoc_slice(member##_buffer, 7);                             \
        member##_buffer[7] = 0;                                                \
      }                                                                        \
      localeconv_result.member = member##_buffer;                              \
    } while(0)

  __CPROVER_LCONV_STRING(decimal_point, '.');
  // the decimal point is never empty
  __CPROVER_assume(localeconv_result.decimal_point[0] != 0);
  __CPROVER_LCONV_STRING(thousands_sep, 0);
  __CPROVER_LCONV_STRING(grouping, 0);
  __CPROVER_LCONV_STRING(mon_decimal_point, 0);
  __CPROVER_LCONV_STRING(mon_thousands_sep, 0);
  __CPROVER_LCONV_STRING(mon_grouping, 0);
  __CPROVER_LCONV_STRING(positive_sign, 0);
  __CPROVER_LCONV_STRING(negative_sign, 0);
  __CPROVER_LCONV_STRING(currency_symbol, 0);
  __CPROVER_LCONV_STRING(int_curr_symbol, 0);
#  undef __CPROVER_LCONV_STRING

#  define __CPROVER_LCONV_CHAR(member)                                         \
    localeconv_result.member = c_locale ? CHAR_MAX : __VERIFIER_nondet_char()

  __CPROVER_LCONV_CHAR(int_frac_digits);
  __CPROVER_LCONV_CHAR(frac_digits);
  __CPROVER_LCONV_CHAR(p_cs_precedes);
  __CPROVER_LCONV_CHAR(p_sep_by_space);
  __CPROVER_LCONV_CHAR(n_cs_precedes);
  __CPROVER_LCONV_CHAR(n_sep_by_space);
  __CPROVER_LCONV_CHAR(p_sign_posn);
  __CPROVER_LCONV_CHAR(n_sign_posn);
#  ifndef _WIN32
  // added in C99, not available with the Windows UCRT
  __CPROVER_LCONV_CHAR(int_p_cs_precedes);
  __CPROVER_LCONV_CHAR(int_n_cs_precedes);
  __CPROVER_LCONV_CHAR(int_p_sep_by_space);
  __CPROVER_LCONV_CHAR(int_n_sep_by_space);
  __CPROVER_LCONV_CHAR(int_p_sign_posn);
  __CPROVER_LCONV_CHAR(int_n_sign_posn);
#  endif
#  undef __CPROVER_LCONV_CHAR

  return &localeconv_result;
#endif
}
