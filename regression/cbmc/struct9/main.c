#include <assert.h>

struct inner_struct {
  char *GUARDp;
};

struct outer_struct {
  char GUARD;
  struct inner_struct inner;
};

void foo(struct inner_struct *inner)
{
  assert(*(inner->GUARDp) != 1);
}

int main()
{
  struct outer_struct outer;

  outer.GUARD = 2;
  outer.inner.GUARDp = &outer.GUARD;

  foo(&outer.inner);
}
