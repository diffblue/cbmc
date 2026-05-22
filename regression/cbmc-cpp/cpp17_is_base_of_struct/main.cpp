// Per N5008 [meta.rel] table:
// `is_base_of<Base, Derived>::value` is true iff `Base` is a base of
// `Derived`, regardless of whether the types are declared with `class`
// or `struct`.  CBMC's `__is_base_of` builtin must accept both.
#include <type_traits>

struct base_t {};
struct derived_t : base_t {};

static_assert(std::is_base_of<base_t, derived_t>::value, "derived_t derives from base_t");
static_assert(std::is_base_of<base_t, base_t>::value, "base_t is its own base");
static_assert(!std::is_base_of<derived_t, base_t>::value, "base_t does not derive from derived_t");

int main()
{
  return 0;
}
