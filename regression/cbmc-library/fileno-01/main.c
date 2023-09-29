#include <assert.h>
#include <stdio.h>

int main()
{
  int fd;
  FILE *some_file = fdopen(fd, "");
  if(some_file)
    assert(fileno(some_file) >= -1);

  return 0;
}
