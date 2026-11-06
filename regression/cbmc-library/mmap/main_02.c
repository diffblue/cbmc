#ifndef _WIN32

#  include <sys/mman.h>

#  include <assert.h>

int main(void)
{
  // POSIX.1-2017 mmap: may return MAP_FAILED.
  void *p =
    mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  // Assert it always succeeds: must FAIL, proving MAP_FAILED is reachable.
  assert(p != MAP_FAILED);

  return 0;
}

#else

int main(void)
{
  return 0;
}

#endif
