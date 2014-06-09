/* FUNCTION: err */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void err(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  abort();
}

/* FUNCTION: err */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

void errx(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  abort();
}

/* FUNCTION: warn */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void warn(const char *fmt, ...)
{
  (void)*fmt;
}

/* FUNCTION: warnx */

#ifndef __CPROVER_ERR_H_INCLUDED
#include <err.h>
#define __CPROVER_ERR_H_INCLUDED
#endif

void warnx(const char *fmt, ...)
{
  (void)*fmt;
}
