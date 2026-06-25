// Companion to ms_extensions_anonymous_member, compiled WITHOUT
// -fms-extensions.  Without that flag goto-cc follows standard gcc/Clang
// behaviour: a *tagged* struct/union used as an anonymous member declares
// nothing -- it injects no members and contributes no size.  The
// _Static_assert (checked at conversion time) therefore requires the
// enclosing struct to be sized as if the tagged member were absent.
// Member types are fixed-width so the expected size holds on 32-bit and
// 64-bit targets.
struct head
{
  int name;
  int refcnt;
  int aname;
};

struct filename
{
  struct
    head; // anonymous tagged-struct member: ignored without -fms-extensions
  char iname[20];
};

// The tagged member contributes no size, so the struct is just char[20].
_Static_assert(sizeof(struct filename) == 20, "tagged anon member ignored");

int main(void)
{
  struct filename f;
  (void)f;
  return 0;
}
