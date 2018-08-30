/* FUNCTION: gethostbyname */

#ifdef _MSC_VER
#include <windows.h>
#else
#include <netdb.h>
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

struct hostent *gethostbyname(const char *name)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(name),
                         "gethostbyname zero-termination of name argument");
  #endif
  (void)*name;

  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error) return 0;

  // quite restrictive, as will alias between calls
  static struct hostent result;

  // we whould be filling in the fields of this
  return &result;
}

/* FUNCTION: gethostbyaddr */

#ifdef _MSC_VER
#include <windows.h>
#else
#include <netdb.h>
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

struct hostent *gethostbyaddr(const void *addr, socklen_t len, int type)
{
  __CPROVER_HIDE:;
  (void)*(char*)addr;
  (void)len;
  (void)type;

  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error) return 0;

  // quite restrictive, as will alias between calls
  static struct hostent result;

  // we whould be filling in the fields of this
  return &result;
}

/* FUNCTION: gethostent */

// There does not appear to be a Windows variant of gethostent
#include <netdb.h>

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

struct hostent *gethostent(void)
{
  __CPROVER_HIDE:;

  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error) return 0;

  // quite restrictive, as will alias between calls
  static struct hostent result;

  // we whould be filling in the fields of this
  return &result;
}
