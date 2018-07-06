#include <inttypes.h>
#include <stdio.h>
#include <sys/mman.h>

#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

void *mapmem(off_t offset, size_t length)
{
  int fd;
  uint8_t *mem, *tmp;
  const int prot = PROT_READ | PROT_WRITE;
  const int flags = MAP_SHARED;

  mem = NULL;
  fd = open("/dev/mem", O_RDWR | O_CLOEXEC);
  if(fd == -1)
    goto out;

  tmp = mmap(NULL, length, prot, flags, fd, offset);
  close(fd);
  if(tmp == MAP_FAILED)
    goto out;
  mem = tmp;
out:
  return mem;
}

int main()
{
  unsigned int target = 0xffffff;
  uint8_t *mem;
  mem = mapmem(target, 1024L);
  printf("got address %p from target %p\n", mem, (unsigned int *)target);
  return 0;
}
