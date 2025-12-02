/* FUNCTION: time */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef time

time_t __VERIFIER_nondet_time_t(void);
time_t __time64(time_t *);

time_t time(time_t *tloc)
{
  return __time64(tloc);
}

/* FUNCTION: __time64 */

#ifndef __CPROVER_TIME_H_INCLUDED
#  include <time.h>
#  define __CPROVER_TIME_H_INCLUDED
#endif

time_t __VERIFIER_nondet_time_t(void);

time_t __time64(time_t *tloc)
{
  time_t res=__VERIFIER_nondet_time_t();
  if(tloc)
    *tloc = res;
  return res;
}

/* FUNCTION: _time64 */

#ifdef _WIN32

#  ifndef __CPROVER_TIME_H_INCLUDED
#    include <time.h>
#    define __CPROVER_TIME_H_INCLUDED
#  endif

time_t __VERIFIER_nondet_time_t(void);

time_t _time64(time_t *tloc)
{
  time_t res = __VERIFIER_nondet_time_t();
  if(tloc)
    *tloc = res;
  return res;
}

#endif

/* FUNCTION: _time32 */

#if defined(_WIN32) && defined(_USE_32BIT_TIME_T)

#  ifndef __CPROVER_TIME_H_INCLUDED
#    include <time.h>
#    define __CPROVER_TIME_H_INCLUDED
#  endif

__time32_t __VERIFIER_nondet_time32_t(void);

__time32_t _time32(__time32_t *tloc)
{
  __time32_t res = __VERIFIER_nondet_time32_t();
  if(tloc)
    *tloc = res;
  return res;
}

#endif

/* FUNCTION: gmtime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef gmtime

struct tm *gmtime(const time_t *clock)
{
  // not very general, may be too restrictive
  // need to set the fields to something meaningful
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "gmtime_result");
  struct tm *gmtime_result;
  __CPROVER_set_must(gmtime_result, "gmtime_result");
  return gmtime_result;
  #else
  static struct tm return_value;
  return &return_value;
  #endif
}

/* FUNCTION: gmtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef gmtime

struct tm *gmtime_r(const time_t *clock, struct tm *result)
{
  // need to set the fields to something meaningful
  (void)*clock;
  return result;
}

/* FUNCTION: localtime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

struct tm *localtime(const time_t *clock)
{
  // not very general, may be too restrictive
  // need to set the fields to something meaningful
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "localtime_result");
  struct tm *localtime_result;
  __CPROVER_set_must(localtime_result, "localtime_result");
  return localtime_result;
  #else
  static struct tm return_value;
  return &return_value;
  #endif
}

/* FUNCTION: localtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

struct tm *localtime_r(const time_t *clock, struct tm *result)
{
  // need to set the fields to something meaningful
  (void)*clock;
  return result;
}

/* FUNCTION: mktime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef mktime

time_t __VERIFIER_nondet_time_t(void);

time_t mktime(struct tm *timeptr)
{
  (void)*timeptr;
  time_t result=__VERIFIER_nondet_time_t();
  return result;
}

/* FUNCTION: timegm */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef timegm

time_t __VERIFIER_nondet_time_t(void);

time_t timegm(struct tm *timeptr)
{
  (void)*timeptr;
  time_t result=__VERIFIER_nondet_time_t();
  return result;
}

/* FUNCTION: asctime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

char *asctime(const struct tm *timeptr)
{
  (void)*timeptr;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "asctime_result");
  char *asctime_result;
  __CPROVER_set_must(asctime_result, "asctime_result");
  return asctime_result;
  #else
  static char asctime_result[1];
  return asctime_result;
  #endif
}

/* FUNCTION: ctime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

char *ctime(const time_t *clock)
{
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "ctime_result");
  char *ctime_result;
  __CPROVER_set_must(ctime_result, "ctime_result");
  return ctime_result;
  #else
  static char ctime_result[1];
  return ctime_result;
  #endif
}

/* FUNCTION: strftime */

#ifndef __CPROVER_TIME_H_INCLUDED
#  include <time.h>
#  define __CPROVER_TIME_H_INCLUDED
#endif

__CPROVER_size_t __VERIFIER_nondet_size_t(void);

__CPROVER_size_t
strftime(char *s, __CPROVER_size_t max, const char *format, const struct tm *tm)
{
  (void)*format;
  (void)*tm;
  __CPROVER_havoc_slice(s, max);
  __CPROVER_size_t length = __VERIFIER_nondet_size_t();
  if(length >= max)
    return 0;
  s[length] = '\0';
  return length;
}

/* FUNCTION: _strftime */

#ifndef __CPROVER_TIME_H_INCLUDED
#  include <time.h>
#  define __CPROVER_TIME_H_INCLUDED
#endif

__CPROVER_size_t __VERIFIER_nondet_size_t(void);

__CPROVER_size_t _strftime(
  char *s,
  __CPROVER_size_t max,
  const char *format,
  const struct tm *tm)
{
  (void)*format;
  (void)*tm;
  __CPROVER_havoc_slice(s, max);
  __CPROVER_size_t length = __VERIFIER_nondet_size_t();
  if(length >= max)
    return 0;
  s[length] = '\0';
  return length;
}

/* FUNCTION: clock_gettime */

#ifndef __CPROVER_TIME_H_INCLUDED
#  include <time.h>
#  define __CPROVER_TIME_H_INCLUDED
#endif

#ifndef __CPROVER_ERRNO_H_INCLUDED
#  include <errno.h>
#  define __CPROVER_ERRNO_H_INCLUDED
#endif

int __VERIFIER_nondet_int(void);
time_t __VERIFIER_nondet_time_t(void);
long __VERIFIER_nondet_long(void);

#ifdef _WIN32
typedef int clockid_t;
#endif

int clock_gettime(clockid_t clockid, struct timespec *tp)
{
__CPROVER_HIDE:;

  // Use the clockid parameter (all clock types are modeled the same way)
  (void)clockid;

  // Check for null pointer - should set errno to EFAULT
  // Some systems have C headers where `tp` is annotated to be nonnull
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wnonnull-compare"
  if(!tp)
  {
    errno = EFAULT;
    return -1;
  }
#pragma GCC diagnostic pop

  // Non-deterministically choose success or failure
  int result = __VERIFIER_nondet_int();

  if(result == 0)
  {
    // Success case: fill in the timespec structure with non-deterministic but valid values
    time_t sec = __VERIFIER_nondet_time_t();
    // Assume reasonable time values (non-negative for typical use cases)
    __CPROVER_assume(sec >= 0);
    tp->tv_sec = sec;

    // Nanoseconds should be between 0 and 999,999,999
    long nanosec = __VERIFIER_nondet_long();
    __CPROVER_assume(nanosec >= 0 && nanosec <= 999999999L);
    tp->tv_nsec = nanosec;

    return 0;
  }
  else
  {
    // Failure case: set errno and return -1
    int error_code = __VERIFIER_nondet_int();
    // Most common error codes for clock_gettime
    __CPROVER_assume(
      error_code == EINVAL || error_code == EACCES || error_code == ENODEV ||
      error_code == ENOTSUP || error_code == EOVERFLOW || error_code == EPERM);
    errno = error_code;
    return -1;
  }
}
