// N5008 [meta.unary.prop] Table 54: is_nothrow_constructible<int &, C>
// requires `int &t(declval<C>());' to be known not to throw; C's
// conversion function is potentially-throwing ([except.spec]/3).
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
int g;
struct C
{
  operator int &()
  {
    return g;
  }
};
int main()
{
  __CPROVER_assert(
    !std::is_nothrow_constructible<int &, C>::value,
    "throwing conversion to a reference");
  __CPROVER_assert(
    std::is_nothrow_constructible<int &, C>::value, "WRONG (must FAIL)");
}
