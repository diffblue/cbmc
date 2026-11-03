/* FUNCTION: gethostbyname */

#ifdef _MSC_VER
#include <windows.h>
#else
#include <netdb.h>
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

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

  // Fill in fields per POSIX.1-2017 netdb.h.
  static char h_name_buf[1];
  result.h_name = h_name_buf;
  static char *h_aliases_list[1];
  h_aliases_list[0] = (char *)0;
  result.h_aliases = h_aliases_list;
  result.h_addrtype = __VERIFIER_nondet_int();
  result.h_length = 4;
  // h_addr_list: at least one entry, NULL-terminated.
  static char h_addr_buf[4];
  static char *h_addr_list_buf[2];
  h_addr_list_buf[0] = h_addr_buf;
  h_addr_list_buf[1] = (char *)0;
  result.h_addr_list = h_addr_list_buf;
  return &result;
}

/* FUNCTION: gethostbyaddr */

#ifdef _MSC_VER
#include <windows.h>
#else
#include <netdb.h>
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

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

  static char h_name_buf[1];
  result.h_name = h_name_buf;
  static char *h_aliases_list[1];
  h_aliases_list[0] = (char *)0;
  result.h_aliases = h_aliases_list;
  result.h_addrtype = __VERIFIER_nondet_int();
  result.h_length = 4;
  static char h_addr_buf[4];
  static char *h_addr_list_buf[2];
  h_addr_list_buf[0] = h_addr_buf;
  h_addr_list_buf[1] = (char *)0;
  result.h_addr_list = h_addr_list_buf;
  return &result;
}

/* FUNCTION: gethostent */

// There does not appear to be a Windows variant of gethostent
#include <netdb.h>

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

struct hostent *gethostent(void)
{
  __CPROVER_HIDE:;

  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  if(error) return 0;

  // quite restrictive, as will alias between calls
  static struct hostent result;

  // POSIX.1-2017 netdb.h: fill in fields.
  static char h_name_buf[1];
  result.h_name = h_name_buf;
  static char *h_aliases_list[1];
  h_aliases_list[0] = (char *)0;
  result.h_aliases = h_aliases_list;
  result.h_addrtype = __VERIFIER_nondet_int();
  result.h_length = 4;
  // h_addr_list: NULL-terminated array with at least one entry.
  static char h_addr_buf[4];
  static char *h_addr_list_buf[2];
  h_addr_list_buf[0] = h_addr_buf;
  h_addr_list_buf[1] = (char *)0;
  result.h_addr_list = h_addr_list_buf;
  return &result;
}
