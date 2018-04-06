#ifdef LIBRARY_CHECK
#include <locale.h>
#endif

/* FUNCTION: setlocale */

inline char *setlocale(int category, const char *locale)
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

inline struct lconv *localeconv(void)
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
