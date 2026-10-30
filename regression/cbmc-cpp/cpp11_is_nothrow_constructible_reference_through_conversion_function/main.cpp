// N5008 [meta.unary.prop] Table 54: is_nothrow_constructible<int &, C>
// requires `int &t(declval<C>());' to be known not to throw; C's
// conversion function is potentially-throwing ([except.spec]/3).
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);
int g;
struct Throws
{
  operator int &()
  {
    return g;
  }
};
struct Quiet
{
  operator int &() noexcept
  {
    return g;
  }
};
struct ToCRef
{
  operator long()
  {
    return 1;
  }
};
struct B
{
};
struct D : B
{
};
int main()
{
  __CPROVER_assert(
    !std::is_nothrow_constructible<int &, Throws>::value,
    "throwing conversion");
  __CPROVER_assert(
    std::is_nothrow_constructible<int &, Quiet>::value, "noexcept conversion");
  __CPROVER_assert(
    std::is_nothrow_constructible<int &, int &>::value, "direct binding");
  __CPROVER_assert(
    std::is_nothrow_constructible<const int &, long>::value,
    "temporary of scalar");
  __CPROVER_assert(
    !std::is_nothrow_constructible<const int &, ToCRef>::value,
    "temporary through throwing conversion");
  __CPROVER_assert(
    std::is_nothrow_constructible<B &, D &>::value, "derived to base");
  __CPROVER_assert(
    !std::is_nothrow_constructible<int &, long>::value, "not constructible");
  __CPROVER_assert(
    std::is_nothrow_constructible<int &, Throws>::value, "WRONG (must FAIL)");
}
