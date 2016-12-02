/* FUNCTION: time */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef time

time_t time(time_t *tloc)
{
  time_t res;
  if(!tloc) *tloc=res;
  return res;
}

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

time_t mktime(struct tm *timeptr)
{
  (void)*timeptr;
  time_t result;
  return result;
}

/* FUNCTION: timegm */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef timegm

time_t timegm(struct tm *timeptr)
{
  (void)*timeptr;
  time_t result;
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
