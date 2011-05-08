/* FUNCTION: inet_addr */

#include <arpa/inet.h>

in_addr_t inet_addr(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_addr zero-termination of argument");
  #endif

  in_addr_t result;
  return result;
}

/* FUNCTION: inet_aton */

int inet_aton(const char *cp, struct in_addr *pin)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_aton zero-termination of name argument");
  #endif

  int result;
  return result;
}

/* FUNCTION: inet_network */

in_addr_t inet_network(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(cp), "inet_network zero-termination of name argument");
  #endif

  in_addr_t result;
  return result;
}

