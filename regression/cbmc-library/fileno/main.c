#include <assert.h>
#include <stdio.h>

int main()
{
  // requires initialization of stdin/stdout/stderr
  // assert(fileno(stdin) == 0);
  // assert(fileno(stdout) == 1);
  // assert(fileno(stderr) == 2);

  int fd;
  FILE *some_file = fdopen(fd, "");
  assert(fileno(some_file) >= -1);

  return 0;
}
