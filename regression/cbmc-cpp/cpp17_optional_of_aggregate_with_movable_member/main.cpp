// Regression guard: N5008 [class.copy.ctor]/8 implicit move operations are
// declared by the front end only for classes with a move-only subobject.
// Declaring them for `chk' (a member with a user-provided move constructor)
// made `return {{b, e}}' for std::optional<chk> fail std::optional's
// constructor constraints: "invalid implicit conversion from '<<type:>>' to
// 'struct optional &&'" (CBMC's own local_safe_pointers.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
#include <optional>
struct ex
{
  int id = 0;
  ex() = default;
  ex(int i) : id(i)
  {
  }
  ex(const ex &o) : id(o.id)
  {
  }
  ex(ex &&o) : id(o.id)
  {
  }
  ex &operator=(const ex &) = default;
};
struct chk
{
  bool when;
  ex e;
};
std::optional<chk> get(bool b, const ex &e)
{
  if(b)
    return {{b, e}};
  return {};
}
int main()
{
  auto r = get(true, ex(4));
  __CPROVER_assert(
    r.has_value() && r->e.id == 4 && r->when,
    "optional of an aggregate with a movable member");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
