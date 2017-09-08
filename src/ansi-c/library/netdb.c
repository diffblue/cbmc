/* FUNCTION: gethostbyname */

#include <netdb.h>

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

struct hostent *gethostbyname(const char *name)
{
  __CPROVER_HIDE:;
  (void)*name;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(name), "gethostbyname zero-termination of name argument");
  #endif

  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error) return 0;

  // quite restrictive, as will alias between calls
  static struct hostent result;

  // we whould be filling in the fields of this
  return &result;
}

/* FUNCTION: gethostbyaddr */

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
