#ifndef _WIN32

#  include <sys/mman.h>

#  include <assert.h>
#  include <errno.h>

int main(void)
{
  void *p =
    mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if(p == MAP_FAILED)
    return 0;

  // POSIX.1-2017 munmap: a length of zero is an error
  int r0 = munmap(p, 0);
  assert(r0 == -1 && errno == EINVAL);

  // unmapping a valid mapping does not fail
  int r = munmap(p, 4096);
  assert(r == 0);

  // the mapping is no longer accessible
  *(char *)p = 42;

  return 0;
}

#else

int main(void)
{
  return 0;
}

#endif
