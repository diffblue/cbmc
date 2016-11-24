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
  static struct tm return_value;
  return &return_value;
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
  static struct tm return_value;
  return &return_value;
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

