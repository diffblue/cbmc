#ifndef _WIN32
#ifdef LIBRARY_CHECK
#include <arpa/inet.h>
#undef htonl
#undef htons
#undef ntohl
#undef ntohs
#endif
#endif

/* FUNCTION: inet_addr */

#ifndef _WIN32

in_addr_t __VERIFIER_nondet_in_addr_t();

in_addr_t inet_addr(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_addr zero-termination of argument");
  #endif
  (void)*cp;

  in_addr_t result=__VERIFIER_nondet_in_addr_t();
  return result;
}

#endif

/* FUNCTION: inet_aton */

#ifndef _WIN32

int __VERIFIER_nondet_int();

int inet_aton(const char *cp, struct in_addr *pin)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_aton zero-termination of name argument");
  #endif
  (void)*cp;
  (void)*pin;

  int result=__VERIFIER_nondet_int();
  return result;
}

#endif

/* FUNCTION: inet_network */

#ifndef _WIN32

in_addr_t __VERIFIER_nondet_in_addr_t();

in_addr_t inet_network(const char *cp)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_precondition(__CPROVER_is_zero_string(cp),
                         "inet_network zero-termination of name argument");
  #endif
  (void)*cp;

  in_addr_t result=__VERIFIER_nondet_in_addr_t();
  return result;
}

#endif

/* FUNCTION: htonl */

unsigned int __builtin_bswap32(unsigned int);

unsigned int htonl(unsigned int hostlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap32(hostlong);
#else
  return hostlong;
#endif
}

/* FUNCTION: htons */

unsigned short __builtin_bswap16(unsigned short);

unsigned short htons(unsigned short hostshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap16(hostshort);
#else
  return hostlong;
#endif
}


/* FUNCTION: ntohl */

unsigned int __builtin_bswap32(unsigned int);

unsigned int ntohl(unsigned int netlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap32(netlong);
#else
  return netlong;
#endif
}


/* FUNCTION: ntohs */

unsigned short __builtin_bswap16(unsigned short);

unsigned short ntohs(unsigned short netshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap16(netshort);
#else
  return netshort;
#endif
}
