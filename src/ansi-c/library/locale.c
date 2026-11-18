
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

// The Universal CRT's and mingw-w64's wide-character copies of the strings
// (mingw-w64's <locale.h> declares them under the same condition).
#if defined(_MSC_VER) ||                                                       \
  (defined(__MINGW32__) && (__MSVCRT_VERSION__ >= 0xA00 ||                     \
                            (__MSVCRT_VERSION__ == 0x600 &&                    \
                             defined(_WIN32_WINNT) && _WIN32_WINNT >= 0x601)))
#  define __CPROVER_LCONV_HAS_W_MEMBERS
#  ifndef __CPROVER_STDDEF_H_INCLUDED
#    include <stddef.h>
#    define __CPROVER_STDDEF_H_INCLUDED
#  endif
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
  // C11 7.11p2: decimal_point is ".", the other strings are "", and the char
  // members are CHAR_MAX (not available). Once setlocale has been called
  // with a non-null locale, any locale may be in effect: the strings are
  // then nondeterministic (of up to 7 characters, with a non-empty decimal
  // point), and so are the char members.
  static struct lconv localeconv_result;
  __CPROVER_bool c_locale = !__CPROVER_locale_may_have_changed;

#  define __CPROVER_LCONV_STRING(type, member, c_value)                        \
    do                                                                         \
    {                                                                          \
      static type member##_buffer[8];                                          \
      if(c_locale)                                                             \
      {                                                                        \
        member##_buffer[0] = c_value;                                          \
        member##_buffer[1] = 0;                                                \
      }                                                                        \
      else                                                                     \
      {                                                                        \
        __CPROVER_havoc_slice(member##_buffer, 7 * sizeof(type));              \
        member##_buffer[7] = 0;                                                \
      }                                                                        \
      localeconv_result.member = member##_buffer;                              \
    } while(0)

  __CPROVER_LCONV_STRING(char, decimal_point, '.');
  // the decimal point is never empty
  __CPROVER_assume(localeconv_result.decimal_point[0] != 0);
  __CPROVER_LCONV_STRING(char, thousands_sep, 0);
  __CPROVER_LCONV_STRING(char, grouping, 0);
  __CPROVER_LCONV_STRING(char, mon_decimal_point, 0);
  __CPROVER_LCONV_STRING(char, mon_thousands_sep, 0);
  __CPROVER_LCONV_STRING(char, mon_grouping, 0);
  __CPROVER_LCONV_STRING(char, positive_sign, 0);
  __CPROVER_LCONV_STRING(char, negative_sign, 0);
  __CPROVER_LCONV_STRING(char, currency_symbol, 0);
  __CPROVER_LCONV_STRING(char, int_curr_symbol, 0);
#  ifdef __CPROVER_LCONV_HAS_W_MEMBERS
  __CPROVER_LCONV_STRING(wchar_t, _W_decimal_point, L'.');
  __CPROVER_assume(localeconv_result._W_decimal_point[0] != 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_thousands_sep, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_int_curr_symbol, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_currency_symbol, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_mon_decimal_point, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_mon_thousands_sep, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_positive_sign, 0);
  __CPROVER_LCONV_STRING(wchar_t, _W_negative_sign, 0);
#  endif
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
  // added in C99, not available with the Windows C libraries
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

#undef __CPROVER_LCONV_HAS_W_MEMBERS

/* FUNCTION: uselocale */

// POSIX.1-2024: uselocale sets the current thread's locale to newloc, unless
// it is (locale_t)0, and returns the locale in effect before -- initially
// LC_GLOBAL_LOCALE.  libc++ switches to its "C" locale with it around the
// C library's formatting (libstdc++ uses __uselocale, see below).
// newloc is assumed to be LC_GLOBAL_LOCALE or a valid locale object: the
// EINVAL failure for invalid handles is not modelled, as there are no
// newlocale/freelocale models to check validity against.

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

/* FUNCTION: __uselocale */

// glibc's name of uselocale, which libstdc++ calls (via __gnu_cxx::__uselocale)
// around the C library's formatting of floating-point numbers.

#ifndef __CPROVER_LOCALE_H_INCLUDED
#  include <locale.h>
#  define __CPROVER_LOCALE_H_INCLUDED
#endif

#ifdef __GLIBC__

locale_t uselocale(locale_t);

locale_t __uselocale(locale_t newloc)
{
__CPROVER_HIDE:;
  return uselocale(newloc);
}

#endif
