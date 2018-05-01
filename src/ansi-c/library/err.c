/* FUNCTION: err */

void abort(void);

void err(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  abort();
}

/* FUNCTION: err */

void abort(void);

void errx(int eval, const char *fmt, ...)
{
  (void)eval;
  (void)*fmt;
  abort();
}

/* FUNCTION: warn */

void warn(const char *fmt, ...)
{
  (void)*fmt;
}

/* FUNCTION: warnx */

void warnx(const char *fmt, ...)
{
  (void)*fmt;
}
