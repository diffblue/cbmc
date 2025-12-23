#include <sys/mman.h>

#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

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
  unsigned long int target = 0xffffffL;
  uint8_t *mem;
  mem = mapmem(target, 1024L);
  printf("got address %p from target %p\n", mem, (void *)target);
  mem[0] = 42;
  munmap(mem, 1024L);
  return 0;
}
