#include <assert.h>
#include <syslog.h>

int main()
{
  syslog();
  assert(0);
  return 0;
}
