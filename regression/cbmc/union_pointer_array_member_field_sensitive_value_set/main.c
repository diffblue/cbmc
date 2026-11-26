#include <assert.h>

// A struct placed at the start of a union, as MSVC's std::function places
// its target in its small-object buffer, whose last pointer element points
// to it.  The stored pointers are read back through the union.
struct vt
{
  int (*call)(void);
};
int two(void)
{
  return 2;
}
const struct vt the_vt = {two};
struct base
{
  const struct vt *vptr;
};
union storage
{
  char space[56];
  struct base *ptrs[8];
};
struct function
{
  union storage st;
};
int main()
{
  struct function fn;
  struct base *o = (struct base *)&fn.st;
  o->vptr = &the_vt;
  fn.st.ptrs[7] = o;
  struct base *g = fn.st.ptrs[7];
  assert(g->vptr->call() == 2);
  assert(g->vptr->call() == 3);
  return 0;
}
