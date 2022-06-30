#include <assert.h>

struct PtrWrapperInner
{
  int *value;
};

struct PtrWrapper
{
  int *value;
  struct PtrWrapperInner inner;
};

struct AltPtrWrapperInner
{
  int *value;
};

struct AltPtrWrapper
{
  unsigned int *value;
  // A) Doesn't work
  struct AltPtrWrapperInner inner;
  // B) Works
  // struct PtrWrapperInner inner;
};

void fn(struct PtrWrapper wrapper)
{
  assert(*wrapper.value == 10);
  assert(*wrapper.inner.value == 10);
}

int main()
{
  int ret = 10;
  int *ptr = &ret;

  struct AltPtrWrapper alt;
  alt.inner.value = ptr;
  alt.value = ptr;

  // Casting the structure itself works.
  struct PtrWrapper wrapper = *(struct PtrWrapper *)&alt;
  assert(*wrapper.value == 10);
  assert(*wrapper.inner.value == 10);

  // This only works if there is one level of casting.
  int (*alias)(struct AltPtrWrapper) = (int (*)(struct AltPtrWrapper))fn;
  alias(alt);
}
