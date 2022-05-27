/* FUNCTION: getrandom */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

#if defined(__GLIBC__) &&                                                      \
  (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 25))

#  ifndef __CPROVER_SYS_RANDOM_H_INCLUDED
#    include <sys/random.h>
#    define __CPROVER_SYS_RANDOM_H_INCLUDED
#  endif

#  ifndef GRND_NONBLOCK
#    define GRND_NONBLOCK 0
#  endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();
size_t __VERIFIER_nondet_size_t();

ssize_t getrandom(void *buf, size_t buflen, unsigned int flags)
{
  if(flags & GRND_NONBLOCK && __VERIFIER_nondet___CPROVER_bool())
    return -1;

  char bytes[buflen];
  __CPROVER_array_replace(buf, bytes);

  size_t actual_bytes = __VERIFIER_nondet_size_t();
  __CPROVER_assume(actual_bytes <= buflen);
  return (ssize_t)actual_bytes;
}

#endif
