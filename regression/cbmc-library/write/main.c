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
  // errno must be set on write error path
  errno = 0;
  ssize_t w = write(1, "x", 1);
  if(w == -1)
    assert(errno != 0); // POSIX: errno set on error

  return 0;
}
#endif
