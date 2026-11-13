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
  // POSIX.1-2017 close(): EBADF when fildes is not an open fd
  if(close(-1) == -1)
  {
    assert(errno == EBADF);
    assert(0 && "error path of close() reached"); // must be reachable
  }
  return 0;
}
#endif
