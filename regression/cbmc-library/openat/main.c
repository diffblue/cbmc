#include <fcntl.h>

int main()
{
  int dirfd;
  char *unint_path;
  int flags;
  int fd = openat(dirfd, unint_path, flags);
  return 0;
}
