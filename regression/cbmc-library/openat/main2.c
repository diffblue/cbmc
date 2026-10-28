#ifdef _WIN32
int main(void)
{
  return 0;
}
#else
#  include <assert.h>
#  include <fcntl.h>

int main(void)
{
  // POSIX.1-2017: AT_FDCWD means use the current working directory
  int fd = openat(AT_FDCWD, "/dev/null", O_RDONLY);
  if(fd >= 0)
  {
    assert(0); // must be reachable
  }
  return 0;
}
#endif
