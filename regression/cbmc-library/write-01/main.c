#include <limits.h>
#include <unistd.h>

extern const __CPROVER_size_t SIZE;

int main()
{
  __CPROVER_assume(SIZE < SSIZE_MAX);

  int fd;
  char ptr[SIZE];
  __CPROVER_size_t nbytes;

  __CPROVER_assume(fd >= 0);
  __CPROVER_assume(nbytes < SIZE);

  write(fd, ptr, nbytes);
}
