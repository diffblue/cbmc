#include <stdlib.h>
#include <string.h>

int main()
{
  size_t size = 4;
  size_t page_size = 4096;
  void *src = "testing";
  void *dest;
  posix_memalign(&dest, page_size, size);
  memcpy(dest, src, size);
  return 0;
}
