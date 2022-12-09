#include <assert.h>
#include <errno.h>

int main(int arc, char *argv[])
{
  // errno expands to use of __errno_location() with glibc
  assert(errno == 0);
  return 0;
}
