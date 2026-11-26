// N5008 [stmt.return]/2 + [dcl.init.list]/3.5: `return {};` in a
// function returning a class type VALUE-INITIALIZES the result object
// (the default constructor runs).
//
// This used to feed the empty braced-init-list into converting-
// constructor overload resolution instead: for std::optional the
// _Requires SFINAE default template argument of optional(_Up&&) then
// failed with "missing type in template argument" (the front-end
// recovery left callers incomplete -- the goto_trace.cpp dog-food
// CONVERSION ERROR), and an optional built this way was not reliably
// empty.  Fixed by value-initializing the returned temporary before
// constructor overload resolution.
extern "C" void __CPROVER_assert(bool, const char *);
#include <optional>

class C
{
public:
  int data;
};

static std::optional<C> f(bool b)
{
  if(b)
    return C{7};
  return {};
}

int main()
{
  auto o = f(true);
  __CPROVER_assert(o.has_value() && o->data == 7, "engaged value");
  auto e = f(false);
  __CPROVER_assert(!e.has_value(), "return {} is disengaged");
  return 0;
}
