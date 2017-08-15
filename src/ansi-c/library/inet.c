/* FUNCTION: inet_addr */

#include <arpa/inet.h>

in_addr_t __VERIFIER_nondet_in_addr_t();

in_addr_t inet_addr(const char *cp)
{
  __CPROVER_HIDE:;
  (void)*cp;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_addr zero-termination of argument");
  #endif

  in_addr_t result=__VERIFIER_nondet_in_addr_t();
  return result;
}

/* FUNCTION: inet_aton */

int __VERIFIER_nondet_int();

int inet_aton(const char *cp, struct in_addr *pin)
{
  __CPROVER_HIDE:;
  (void)*cp;
  (void)*pin;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_aton zero-termination of name argument");
  #endif

  int result=__VERIFIER_nondet_int();
  return result;
}

/* FUNCTION: inet_network */

in_addr_t __VERIFIER_nondet_in_addr_t();

in_addr_t inet_network(const char *cp)
{
  __CPROVER_HIDE:;
  (void)*cp;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_network zero-termination of name argument");
  #endif

  in_addr_t result=__VERIFIER_nondet_in_addr_t();
  return result;
}
