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

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

struct tm *gmtime(const time_t *clock)
{
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "gmtime_result");
  struct tm *gmtime_result;
  __CPROVER_set_must(gmtime_result, "gmtime_result");
  return gmtime_result;
  #else
  // C11 7.27.3.3: may return a null pointer.
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
    return (struct tm *)0;
  static struct tm return_value;
  // Fill with nondeterministic values in valid ranges (C11 7.27.1).
  return_value.tm_sec = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_sec >= 0 && return_value.tm_sec <= 60);
  return_value.tm_min = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_min >= 0 && return_value.tm_min <= 59);
  return_value.tm_hour = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_hour >= 0 && return_value.tm_hour <= 23);
  return_value.tm_mday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_mday >= 1 && return_value.tm_mday <= 31);
  return_value.tm_mon = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_mon >= 0 && return_value.tm_mon <= 11);
  return_value.tm_year = __VERIFIER_nondet_int();
  return_value.tm_wday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_wday >= 0 && return_value.tm_wday <= 6);
  return_value.tm_yday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_yday >= 0 && return_value.tm_yday <= 365);
  return_value.tm_isdst = 0;
  return &return_value;
  #endif
}

/* FUNCTION: gmtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef gmtime

int __VERIFIER_nondet_int(void);

struct tm *gmtime_r(const time_t *clock, struct tm *result)
{
  (void)*clock;
  // Fill *result with nondeterministic values in valid ranges.
  result->tm_sec = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_sec >= 0 && result->tm_sec <= 60);
  result->tm_min = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_min >= 0 && result->tm_min <= 59);
  result->tm_hour = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_hour >= 0 && result->tm_hour <= 23);
  result->tm_mday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_mday >= 1 && result->tm_mday <= 31);
  result->tm_mon = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_mon >= 0 && result->tm_mon <= 11);
  result->tm_year = __VERIFIER_nondet_int();
  result->tm_wday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_wday >= 0 && result->tm_wday <= 6);
  result->tm_yday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_yday >= 0 && result->tm_yday <= 365);
  result->tm_isdst = 0;
  return result;
}

/* FUNCTION: localtime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
int __VERIFIER_nondet_int(void);

struct tm *localtime(const time_t *clock)
{
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "localtime_result");
  struct tm *localtime_result;
  __CPROVER_set_must(localtime_result, "localtime_result");
  return localtime_result;
  #else
  // C11 7.27.3.4: may return a null pointer.
  __CPROVER_bool error = __VERIFIER_nondet___CPROVER_bool();
  if(error)
    return (struct tm *)0;
  static struct tm return_value;
  return_value.tm_sec = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_sec >= 0 && return_value.tm_sec <= 60);
  return_value.tm_min = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_min >= 0 && return_value.tm_min <= 59);
  return_value.tm_hour = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_hour >= 0 && return_value.tm_hour <= 23);
  return_value.tm_mday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_mday >= 1 && return_value.tm_mday <= 31);
  return_value.tm_mon = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_mon >= 0 && return_value.tm_mon <= 11);
  return_value.tm_year = __VERIFIER_nondet_int();
  return_value.tm_wday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_wday >= 0 && return_value.tm_wday <= 6);
  return_value.tm_yday = __VERIFIER_nondet_int();
  __CPROVER_assume(return_value.tm_yday >= 0 && return_value.tm_yday <= 365);
  return_value.tm_isdst = __VERIFIER_nondet_int();
  return &return_value;
  #endif
}

/* FUNCTION: localtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

int __VERIFIER_nondet_int(void);

struct tm *localtime_r(const time_t *clock, struct tm *result)
{
  (void)*clock;
  result->tm_sec = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_sec >= 0 && result->tm_sec <= 60);
  result->tm_min = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_min >= 0 && result->tm_min <= 59);
  result->tm_hour = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_hour >= 0 && result->tm_hour <= 23);
  result->tm_mday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_mday >= 1 && result->tm_mday <= 31);
  result->tm_mon = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_mon >= 0 && result->tm_mon <= 11);
  result->tm_year = __VERIFIER_nondet_int();
  result->tm_wday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_wday >= 0 && result->tm_wday <= 6);
  result->tm_yday = __VERIFIER_nondet_int();
  __CPROVER_assume(result->tm_yday >= 0 && result->tm_yday <= 365);
  result->tm_isdst = __VERIFIER_nondet_int();
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
  // C11 7.27.3.1: "Sun Sep 16 01:03:52 1973\n\0" (26 bytes).
  static char asctime_result[26];
  __CPROVER_havoc_slice(asctime_result, 25);
  asctime_result[25] = '\0';
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
  // C11 7.27.3.2: equivalent to asctime(localtime(clock)).
  static char ctime_result[26];
  __CPROVER_havoc_slice(ctime_result, 25);
  ctime_result[25] = '\0';
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
