#include <assert.h>

// Two further translation units (resolve_a.c, resolve_b.c) each define their
// own file-local (static) function f, while this unit defines a global
// (external linkage) f, all sharing the name f. Each call must resolve to the
// definition mandated by the C standard: internal linkage stays within its
// translation unit, external linkage is shared.
int fa(void); // returns resolve_a.c's static f (== 1)
int fb(void); // returns resolve_b.c's static f (== 2)

int f(void) // the global f
{
  return 3;
}

int main(void)
{
  assert(fa() == 1);
  assert(fb() == 2);
  assert(f() == 3); // resolves to the global f defined above
}
