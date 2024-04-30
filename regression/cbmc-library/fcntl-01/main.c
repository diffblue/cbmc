#include <assert.h>
#include <fcntl.h>

int main()
{
  int flags;
  int fd = open("foo", flags);
  int cmd;
  int result = fcntl(fd, cmd);
  assert(fd >= 0 || result == -1);
  return 0;
}
