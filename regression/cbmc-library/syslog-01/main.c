#include <assert.h>
#ifndef _WIN32
#  include <syslog.h>
#else
void syslog(int priority, const char *format, ...);
#endif

int main(int argc, char *argv[])
{
  int some_priority;
  syslog(some_priority, "%d\n", argc);
  return 0;
}
