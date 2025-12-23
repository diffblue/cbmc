#include <assert.h>
#include <syslog.h>

int main()
{
  closelog();
  assert(0);
  return 0;
}
