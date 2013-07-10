#include <assert.h>
#include <stddef.h>

// from linux/kernel.h
#ifndef container_of
#define container_of(ptr, type, member) ({                      \
        const typeof(((type *) 0)->member) *__mptr = (ptr);     \
        (type *) ((char *) __mptr - offsetof(type, member));})
#endif

struct NetClientState {
  int dummy;
  /* ... */
};

struct NICState {
  struct NetClientState nc;
  struct NetClientState nc2;
  void *opaque;
  /* ... */
};

typedef int OpenEthState;

#define OPEN_ETH_STATE(a) \
    ((OpenEthState *) container_of(nc, struct NICState, nc)->opaque)

#define OPEN_ETH_STATE2(a) \
    ((OpenEthState *) container_of(a, struct NICState, nc2)->opaque)

static struct NetClientState *nc;

int main()
{
  int x=42;

  struct NICState nic;
  nic.opaque = &x;
  nc = &(nic.nc);

  assert(x==42);
  assert(*((int*)nic.opaque) == 42);

  int *xptr = OPEN_ETH_STATE(nc);
  assert(xptr == &x);
  assert(*xptr == 42);

  nc = &(nic.nc2);

  int *xptr2 = OPEN_ETH_STATE2(nc);
  assert(xptr2 == &x);
  assert(*xptr2 == 42);

  return 0;
}

