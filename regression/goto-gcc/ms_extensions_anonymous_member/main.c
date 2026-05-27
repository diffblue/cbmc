// -fms-extensions: a *tagged* struct/union used as an unnamed (anonymous)
// member.  Its members are injected into the enclosing struct and it
// contributes its size.  Used pervasively in the Linux kernel (e.g.
// struct __filename_head embedded in struct filename, whose static_asserts
// require the size to be exact).  The _Static_asserts here are checked at
// conversion time, so this fails to compile unless the anonymous tagged
// member is laid out correctly.  Member types are deliberately fixed-width
// (no pointers, no long) so the expected sizes are identical on 32-bit and
// 64-bit targets.
struct head
{
  int name;
  int refcnt;
  int aname;
};

struct filename
{
  struct head; // anonymous tagged-struct member
  char iname[20];
};

_Static_assert(sizeof(struct head) == 12, "head size");
_Static_assert(sizeof(struct filename) == 32, "filename size");
_Static_assert(
  __builtin_offsetof(struct filename, iname) == 12,
  "iname offset");

// a tagged union as an anonymous member, too
struct u_outer
{
  union inner
  {
    int i;
    char c[4];
  };
  int tail;
};
_Static_assert(sizeof(struct u_outer) == 8, "union-anon size");

int main(void)
{
  struct filename f;
  f.refcnt = 7; // inner field reachable through the anonymous member
  f.name = 0;

  struct u_outer u;
  u.i = 3; // inner union field reachable

  return f.refcnt + u.i;
}
