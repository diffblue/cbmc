#include <assert.h>
#include <syslog.h>

int main()
{
  openlog();
  assert(0);
  return 0;
}
