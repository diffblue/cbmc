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
    ((OpenEthState *) container_of(a, struct NICState, nc)->opaque)

#define OPEN_ETH_STATE2(a) \
    ((OpenEthState *) container_of(a, struct NICState, nc2)->opaque)

static struct NetClientState *nc;

int main()
{
  int x=42;

  struct NICState nic;
#ifndef __GNUC__
  int *xptr=0, *xptr2=0;
  const struct NetClientState *__mptr1=0, *__mptr2=0;
#endif
  nic.opaque = &x;
  nc = &(nic.nc);

  assert(x==42);
  assert(*((int*)nic.opaque) == 42);

#ifdef __GNUC__
  int *xptr = OPEN_ETH_STATE(nc);
#else
  __mptr1 = nc;
  xptr = (OpenEthState *)
    ((struct NICState *)
     ((char *) __mptr1 - offsetof(struct NICState, nc)))->opaque;
#endif
  assert(xptr == &x);
  assert(*xptr == 42);

  nc = &(nic.nc2);

#ifdef __GNUC__
  int *xptr2 = OPEN_ETH_STATE2(nc);
#else
  __mptr2 = nc;
  xptr2 = (OpenEthState *)
    ((struct NICState *)
     ((char *) __mptr2 - offsetof(struct NICState, nc2)))->opaque;
#endif
  assert(xptr2 == &x);
  assert(*xptr2 == 42);

  return 0;
}
