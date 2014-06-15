/* FUNCTION: openlog */

#ifndef __CPROVER_SYSLOG_H_INCLUDED
#include <syslog.h>
#define __CPROVER_SYSLOG_H_INCLUDED
#endif

void openlog(const char *ident, int option, int facility)
{
  (void)*ident;
  (void)option;
  (void)facility;
}

/* FUNCTION: closelog */

#ifndef __CPROVER_SYSLOG_H_INCLUDED
#include <syslog.h>
#define __CPROVER_SYSLOG_H_INCLUDED
#endif

void closelog(void)
{
}

/* FUNCTION: syslog */

#ifndef __CPROVER_SYSLOG_H_INCLUDED
#include <syslog.h>
#define __CPROVER_SYSLOG_H_INCLUDED
#endif

void syslog(int priority, const char *format, ...)
{
  (void)priority;
  (void)*format;
}
