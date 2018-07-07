/* FUNCTION: inet_addr */

#ifndef _WIN32

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

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

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

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

#ifndef __CPROVER_INET_H_INCLUDED
#include <arpa/inet.h>
#define __CPROVER_INET_H_INCLUDED
#endif

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

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef htonl

uint32_t __builtin_bswap32(uint32_t);

uint32_t htonl(uint32_t hostlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap32(hostlong);
#else
  return hostlong;
#endif
}

/* FUNCTION: htons */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef htons

uint16_t __builtin_bswap16(uint16_t);

uint16_t htons(uint16_t hostshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap16(hostshort);
#else
  return hostshort;
#endif
}


/* FUNCTION: ntohl */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef ntohl

uint32_t __builtin_bswap32(uint32_t);

uint32_t ntohl(uint32_t netlong)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap32(netlong);
#else
  return netlong;
#endif
}


/* FUNCTION: ntohs */

#ifndef __CPROVER_STDINT_H_INCLUDED
#include <stdint.h>
#define __CPROVER_STDINT_H_INCLUDED
#endif

#undef ntohs

uint16_t __builtin_bswap16(uint16_t);

uint16_t ntohs(uint16_t netshort)
{
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return __builtin_bswap16(netshort);
#else
  return netshort;
#endif
}
