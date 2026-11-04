#ifdef _WIN32
int main(void)
{
  return 0;
}
#else
#  include <assert.h>
#  include <errno.h>
#  include <unistd.h>

int main(void)
{
  char b[4];
  // Test 1: read should not produce a spurious pointer error
  read(0, b, sizeof b);

  // Test 2: errno must be set on error path
  errno = 0;
  ssize_t r = read(0, b, sizeof b);
  if(r == -1)
    assert(errno != 0); // POSIX: errno set on error

  return 0;
}
#endif
