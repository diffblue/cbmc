#include <sys/syscall.h>

#include <assert.h>
#include <errno.h>
#include <unistd.h>

int main()
{
  long int rc;
  errno = 0;
  rc = syscall(SYS_chmod, "/etc/passwd", 0444);
  assert(!(rc != -1) || (errno == 0));
}
