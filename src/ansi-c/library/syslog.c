/* FUNCTION: openlog */

void openlog(const char *ident, int option, int facility)
{
  (void)*ident;
  (void)option;
  (void)facility;
}

/* FUNCTION: closelog */

void closelog(void)
{
}

/* FUNCTION: syslog */

void syslog(int priority, const char *format, ...)
{
  (void)priority;
  (void)*format;
}

/* FUNCTION: _syslog$DARWIN_EXTSN */

void _syslog$DARWIN_EXTSN(int priority, const char *format, ...)
{
  (void)priority;
  (void)*format;
}

/* FUNCTION: __syslog_chk */

void __syslog_chk(int priority, int flag, const char *format, ...)
{
  (void)priority;
  (void)flag;
  (void)*format;
}
