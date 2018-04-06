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
