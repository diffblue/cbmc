// FreeBSD kernel allocator signatures. The CPROVER library supplies the
// bodies of malloc(size) and free(ptr), and the surplus arguments are ignored.
#include <stddef.h>

struct malloc_type
{
  const char *name;
};
struct malloc_type M_DEVBUF[1];

void *malloc(size_t size, struct malloc_type *type, int flags);
void free(void *addr, struct malloc_type *type);

void release(int *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(p, sizeof(int)))
  __CPROVER_frees()
// clang-format on
{
  free(p, M_DEVBUF);
}

int *acquire(void)
  // clang-format off
  __CPROVER_ensures(
    __CPROVER_return_value == NULL ||
    __CPROVER_is_fresh(__CPROVER_return_value, sizeof(int)))
// clang-format on
{
  return malloc(sizeof(int), M_DEVBUF, 0x102);
}

int main(void)
{
  int *p = acquire();
  if(p)
    release(p);
  return 0;
}
